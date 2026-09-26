/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.SignedSln
import Categorification.Diagrams.KL3.Grading

/-!
# The revised Definition 4.1 of `U→(sl_n)` (Khovanov–Lauda erratum)

M. Khovanov, A. D. Lauda, *Erratum to: "A categorification of quantum sl(n)"*, Quantum Topol. 2
(2011), 97–99, DOI 10.4171/QT/15 (below: **[Err]**), correcting KL III (arXiv:0807.3250v1;
published as Quantum Topol. 1 (2010), 1–92). [Err] replaces Definition 4.1 (published §4.2,
pp. 58–59; arXiv v1 TeX label `def_Ucatq-sln`, formalized as `Signed.presSigned`) by a new
Definition 4.1 ([Err] p. 97, last paragraph, to p. 98). We transcribe it literally as
`Signed.presSignedQT`.

## Reading of the revised Definition 4.1

We use the conventions of `Categorification.Diagrams.KL3.Relations`: diagrams are read bottom to
top, `crossl RD i j μ : E_i F_j ⟶ F_j E_i` and `crossr RD i j μ : F_j E_i ⟶ E_i F_j`, `μ` the
rightmost region; vertices are `Fin m` and `i - j` is computed in `ℤ` (as in `Signed.qSigned`).

* **Objects, 1-morphisms, generators** ([Err] p. 97, Def. 4.1, first sentence): those of
  Definition 3.1. Both `presSigned` and `presSignedQT` are presentations on the same signature
  `psig (slRootDatum m)` over the same pivotal base (cups, caps, zigzags).
* **sl₂ relations, shift isomorphisms** ([Err] p. 97, first bullet: "(3.1)–(3.9)"): unchanged.
* **Cyclicity** ([Err] p. 97, second bullet and its display): generators are cyclic, see (3.3)
  and (3.10) (arXiv labels `eq_cyclic_dot`, `eq_cyclic_cross-gen`), *except when `i · j = -1`*,
  where the displayed relation is: [caps on the left, cups on the right, bottom `j i`, top `i j`]
  `= -` [cups on the left, caps on the right]. Reading the arrows and the nested cups/caps of the
  two pictures, both are `F_j F_i ⟶ F_i F_j` rotations of the upward crossing `E_j E_i ⟶ E_i E_j`:
  the left picture is `rotCrossR RD j i μ`, the right one `rotCrossL RD j i μ`. So for
  `j · i = -1` the relations `cycCrossR j i μ`, `cycCrossL j i μ` (`rotCrossR = downCross =
  rotCrossL`) are replaced by the single relation `rotCrossR j i μ + rotCrossL j i μ = 0`.
  *Literally* nothing else is imposed for adjacent colours: in particular the (generating)
  downward crossing `downCross RD j i μ` is not related to the upward one when `j · i = -1`. We
  transcribe this literally (the relation index `cycCrossL j i μ` then carries the trivial
  relation `0`); see "Remarks" below.
* **Sideways crossings** ([Err] p. 98, first bullet and display): defined as the composites of
  the upward crossing with a cup and a cap. Reading the arrows: the left-hand definition
  (`E_i F_j ⟶ F_j E_i`, region `λ` on the right; cup `1 → F_j E_j` bottom left, upward crossing
  `E_j E_i ⟶ E_i E_j`, cap `E_j F_j → 1` top right) is exactly `crossl RD i j`, and the
  right-hand one (`F_j E_i ⟶ E_i F_j`; cup `1 → E_j F_j` bottom right, upward crossing
  `E_i E_j ⟶ E_j E_i`, cap `F_j E_j → 1` top left) is exactly `crossr RD i j`. These are the first
  composites of arXiv `eq_crossl-gen`, `eq_crossr-gen`, i.e. the definitions already used in
  `Relations.lean`; no change is needed.
* **(3.13)** ([Err] p. 98, "Then the relations (3.13) for `i ≠ j` become", two displays;
  arXiv label `eq_downup_ij-gen`, relations `Rel.downupEF`, `Rel.downupFE`):
  - first display (bottom `i` up, `j` down): `crossl i j ≫ crossr i j = 1` if `i · j = 0` and
    `= (i - j) · 1_{E_i F_j}` if `i · j = -1`;
  - second display (bottom `i` down, `j` up): `crossr j i ≫ crossl j i = 1` if `i · j = 0` and
    `= (j - i) · 1_{F_i E_j}` if `i · j = -1`.
* **Signed `R(ν)` relations** ([Err] p. 98, items (a)–(c)): the same as arXiv (4.11)–(4.14),
  i.e. the KLR relations for `Signed.qSigned` (`relationQ … qSigned`).

[Err] lists exactly these items as the modified ones; all remaining relations of Definition 3.1
(dot cyclicity, bubbles, curls, `decompEF`/`decompFE`, distant-colour crossing cyclicity and
`downup` relations) are kept as in arXiv v1, which is what `relationQT` does.

## The possible slip and the consistent variant

The two (3.13) displays are consistent with each other (both say that `crossl a b` and
`crossr a b`, `a` the upward colour, are mutually inverse up to the sign `a - b`). But
[Err]'s own revised Lemma 6.4 ([Err] p. 97, two displays) says that `Γ` sends the pictured
`crossl j i` to the plain swap and the pictured `crossr i j` to the swap times `-1` exactly
when `j → i` (in KL III's orientation `1 → 2 → ⋯`, i.e. `i = j + 1`). Hence `Γ(crossl a b ≫
crossr a b) = (b - a)`, the opposite of the printed `(a - b)`, while `Γ` satisfies the signed
`R(ν)` relation (a) with the printed sign `(i - j)` for the same indexing
(`Signed.gammaCross_sq`). This is confirmed on the path model in
`Categorification.Flag.GammaErratumCheck`. We therefore also define the consistent variant
`presSignedQT'`, which differs from `presSignedQT` only in the sign of the two adjacent (3.13)
relations: `crossl i j ≫ crossr i j = (j - i)` and `crossr j i ≫ crossl j i = (i - j)`.

## Main definitions and results

* `Signed.relationQT`, `Signed.presSignedQT`: the revised Definition 4.1, literally.
* `Signed.relationQT'`, `Signed.presSignedQT'`: the variant with the (3.13) signs reversed.
* `Signed.relationQT_of_not_revised`, `Signed.relationQT'_of_not_revised`: every relation other
  than the adjacent `downupEF`, `downupFE`, `cycCrossR`, `cycCrossL` is that of `presSigned`
  (arXiv v1 Definition 4.1); the modified relations are given explicitly
  (`relationQT_downupEF_adj`, …).
* `Signed.relationQT'_eq_relationQT`: the two revised presentations agree except for the
  adjacent `downup` relations, where the signs are opposite.
* `presQ_isHomogeneous`, `Signed.presSigned_isHomogeneous`, `Signed.presSignedQT_isHomogeneous`,
  `Signed.presSignedQT'_isHomogeneous`: all these presentations are homogeneous for the degree
  of Definition 3.1.

## Remarks

The literal revised cyclicity leaves the adjacent downward crossing unconstrained. On the path
model `Γ_N` sends it to the map (6.9), which equals the *left* rotation
(`Categorification.Flag.rotCrossLW_eq_crossDn`) and minus the right one
(`Categorification.Flag.rotCrossRW_eq_crossDn`), so the natural completion is
`downCross = rotCrossL = -rotCrossR`; neither completion is printed in [Err], and we do not add
one.
-/

noncomputable section

namespace Categorification.KL3.Diagram

open CategoryTheory StringDiagrams QuantumGroup UDot Presentation MvPolynomial

universe w u v

/-! ### Homogeneity of the KLR relations for general polynomials `Q` -/

section Generic

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : RootDatum C X Y) {k : Type w} [CommRing k]

local notation "HK" => LinDiagram.homDeg k (degK (I := I) (C := C))
local notation "HD" => LinDiagram.homDeg k (deg RD)

/-- The KLR relations with polynomials `Q` are homogeneous for the KLR degree, provided `Q_{cd}`
and `Q̄_{cd}` are weighted homogeneous of the degrees required by KL I/II (as for the KL II
polynomials, `klr_relation_mem`). -/
theorem klrQ_relation_mem (Q : I → I → MvPolynomial (Fin 2) k)
    (hQ : ∀ c d, c ≠ d →
      (Q c d).IsWeightedHomogeneous ![C.dot c c, C.dot d d] (-2 * C.dot c d))
    (hQbar : ∀ c d, c ≠ d → (KLR.qbar (Q c d)).IsWeightedHomogeneous
      ![C.dot c c, C.dot d d, C.dot c c] (-2 * C.dot c d - C.dot c c))
    (r : KLR.Diagram.Rel I) :
    ∃ d, KLR.Diagram.relation k Q r ∈ HK r.dom r.cod d := by
  cases r with
  | sqEq c => exact ⟨_, LinDiagram.of_mem_homDeg _⟩
  | sqNe c d h =>
    refine ⟨-2 * C.dot c d, Submodule.sub_mem _ (degK_mem _ ?_)
      (ncEval_mem_homDeg _ _ ![C.dot c c, C.dot d d] ?_ _ _ (hQ c d h))⟩
    · degK_tac; try (rw [C.symm d c]; ring)
    · intro t; fin_cases t <;> exact degK_mem _ (by degK_tac)
  | slideLEq c =>
    refine ⟨0, Submodule.sub_mem _ (Submodule.sub_mem _ (degK_mem _ ?_) (degK_mem _ ?_))
      (degK_mem _ rfl)⟩ <;> (degK_tac; try ring)
  | slideLNe c d h =>
    refine ⟨C.dot d d - C.dot c d, Submodule.sub_mem _ (degK_mem _ ?_) (degK_mem _ ?_)⟩ <;>
      (degK_tac; try ring)
  | slideREq c =>
    refine ⟨0, Submodule.sub_mem _ (Submodule.sub_mem _ (degK_mem _ ?_) (degK_mem _ ?_))
      (degK_mem _ rfl)⟩ <;> (degK_tac; try ring)
  | slideRNe c d h =>
    refine ⟨C.dot c c - C.dot c d, Submodule.sub_mem _ (degK_mem _ ?_) (degK_mem _ ?_)⟩ <;>
      (degK_tac; try ring)
  | braid c d e h =>
    refine ⟨-C.dot c d - C.dot c e - C.dot d e, Submodule.sub_mem _ (degK_mem _ ?_)
      (degK_mem _ ?_)⟩ <;> (degK_tac; try ring)
  | braidQ c d h =>
    refine ⟨-2 * C.dot c d - C.dot c c, Submodule.sub_mem _ (Submodule.sub_mem _ (degK_mem _ ?_)
      (degK_mem _ ?_)) (ncEval_mem_homDeg _ _ ![C.dot c c, C.dot d d, C.dot c c] ?_ _ _
      (hQbar c d h))⟩
    · degK_tac; try (rw [C.symm d c]; ring)
    · degK_tac; try (rw [C.symm d c]; ring)
    · intro t; fin_cases t <;> exact degK_mem _ (by degK_tac)

/-- A presentation with the pivotal base of `U` and relations `rel'` indexed by `Rel RD` is
homogeneous as soon as each `rel' r` is. -/
theorem addRels_isHomogeneous (rel' : (r : Rel RD) → LinDiagram k r.dom r.cod)
    (h : ∀ r, ∃ d, rel' r ∈ HD r.dom r.cod d) :
    (((pres0 RD k).pivotal (inv RD).toColourDuality).addRels (Rel RD) Rel.dom Rel.cod
      rel').IsHomogeneous (deg RD) := by
  rintro (x | r)
  · exact pres_isHomogeneous (RD := RD) (k := k) (.inl x)
  · exact h r

/-- The relations `relationQ RD k Q` are homogeneous under the hypotheses of
`klrQ_relation_mem`. -/
theorem relationQ_mem (Q : I → I → MvPolynomial (Fin 2) k)
    (hQ : ∀ c d, c ≠ d →
      (Q c d).IsWeightedHomogeneous ![C.dot c c, C.dot d d] (-2 * C.dot c d))
    (hQbar : ∀ c d, c ≠ d → (KLR.qbar (Q c d)).IsWeightedHomogeneous
      ![C.dot c c, C.dot d d, C.dot c c] (-2 * C.dot c d - C.dot c c))
    (r : Rel RD) : ∃ d, relationQ RD k Q r ∈ HD r.dom r.cod d := by
  cases r with
  | klr μ r =>
    obtain ⟨d, hd⟩ := klrQ_relation_mem Q hQ hQbar r
    exact ⟨d, upLin_mem (RD := RD) μ hd⟩
  | cycDotR i μ => exact pres_isHomogeneous (RD := RD) (k := k) (.inr (.cycDotR i μ))
  | cycDotL i μ => exact pres_isHomogeneous (RD := RD) (k := k) (.inr (.cycDotL i μ))
  | cwNeg i lam α h => exact pres_isHomogeneous (RD := RD) (k := k) (.inr (.cwNeg i lam α h))
  | ccwNeg i lam α h => exact pres_isHomogeneous (RD := RD) (k := k) (.inr (.ccwNeg i lam α h))
  | cwOne i lam h => exact pres_isHomogeneous (RD := RD) (k := k) (.inr (.cwOne i lam h))
  | ccwOne i lam h => exact pres_isHomogeneous (RD := RD) (k := k) (.inr (.ccwOne i lam h))
  | curlR i lam => exact pres_isHomogeneous (RD := RD) (k := k) (.inr (.curlR i lam))
  | curlL i μ => exact pres_isHomogeneous (RD := RD) (k := k) (.inr (.curlL i μ))
  | decompEF i lam => exact pres_isHomogeneous (RD := RD) (k := k) (.inr (.decompEF i lam))
  | decompFE i lam => exact pres_isHomogeneous (RD := RD) (k := k) (.inr (.decompFE i lam))
  | cycCrossR j i μ => exact pres_isHomogeneous (RD := RD) (k := k) (.inr (.cycCrossR j i μ))
  | cycCrossL j i μ => exact pres_isHomogeneous (RD := RD) (k := k) (.inr (.cycCrossL j i μ))
  | downupEF i j h μ => exact pres_isHomogeneous (RD := RD) (k := k) (.inr (.downupEF i j h μ))
  | downupFE i j h μ => exact pres_isHomogeneous (RD := RD) (k := k) (.inr (.downupFE i j h μ))

/-- **`presQ RD k Q` is homogeneous** whenever `Q_{cd}`, `Q̄_{cd}` are weighted homogeneous of the
KLR degrees. -/
theorem presQ_isHomogeneous (Q : I → I → MvPolynomial (Fin 2) k)
    (hQ : ∀ c d, c ≠ d →
      (Q c d).IsWeightedHomogeneous ![C.dot c c, C.dot d d] (-2 * C.dot c d))
    (hQbar : ∀ c d, c ≠ d → (KLR.qbar (Q c d)).IsWeightedHomogeneous
      ![C.dot c c, C.dot d d, C.dot c c] (-2 * C.dot c d - C.dot c c)) :
    (presQ RD k Q).IsHomogeneous (deg RD) :=
  addRels_isHomogeneous RD _ (relationQ_mem RD Q hQ hQbar)

end Generic

namespace Signed

open Flag

variable (k : Type w) [CommRing k] (m : ℕ)

local notation "SRD" => slRootDatum m
local notation "HD" => LinDiagram.homDeg k (deg (slRootDatum m))

/-! ### The revised Definition 4.1 -/

open LinDiagram in
/-- **The relations of the revised Definition 4.1** ([Err] pp. 97–98), transcribed literally.
For `i · j = -1`:
* `downupEF i j`: `crossl i j ≫ crossr i j - (i - j) · 1` ([Err] p. 98, first (3.13) display);
* `downupFE i j`: `crossr j i ≫ crossl j i - (j - i) · 1` ([Err] p. 98, second (3.13) display);
* `cycCrossR j i`: `rotCrossR j i + rotCrossL j i` ([Err] p. 97, cyclicity display: the left
  picture equals minus the right picture);
* `cycCrossL j i`: `0` (for adjacent colours [Err] imposes no other cyclicity relation on the
  crossing).

All other relations are those of arXiv v1 Definition 4.1 (`relationQ … (qSigned k m)`). -/
def relationQT : (r : Rel SRD) → LinDiagram k r.dom r.cod
  | .downupEF i j h μ =>
    if (slCartan m).dot i j = -1 then
      of (crossl SRD i j μ ≫ crossr SRD i j μ) -
        (((((i : ℕ) : ℤ) - ((j : ℕ) : ℤ) : ℤ) : k) • of (𝟙 _))
    else relation (RD := SRD) k (.downupEF i j h μ)
  | .downupFE i j h μ =>
    if (slCartan m).dot i j = -1 then
      of (crossr SRD j i μ ≫ crossl SRD j i μ) -
        (((((j : ℕ) : ℤ) - ((i : ℕ) : ℤ) : ℤ) : k) • of (𝟙 _))
    else relation (RD := SRD) k (.downupFE i j h μ)
  | .cycCrossR j i μ =>
    if (slCartan m).dot j i = -1 then of (rotCrossR SRD j i μ) + of (rotCrossL SRD j i μ)
    else relation (RD := SRD) k (.cycCrossR j i μ)
  | .cycCrossL j i μ =>
    if (slCartan m).dot j i = -1 then 0
    else relation (RD := SRD) k (.cycCrossL j i μ)
  | r => relationQ SRD k (qSigned k m) r

/-- **The revised Definition 4.1 of KL III** ([Err], Quantum Topol. 2 (2011), pp. 97–98), as a
presentation: the pivotal base of `U` with the relations `relationQT`. -/
def presSignedQT : Presentation.{w, 0} (psig (slRootDatum m)) k :=
  ((pres0 SRD k).pivotal (inv SRD).toColourDuality).addRels (Rel SRD) Rel.dom Rel.cod
    (relationQT k m)

open LinDiagram in
/-- **The consistent variant of the revised Definition 4.1**: `relationQT` with the signs of the
two adjacent (3.13) relations reversed, `crossl i j ≫ crossr i j = (j - i)` and
`crossr j i ≫ crossl j i = (i - j)` for `i · j = -1` (see the module docstring and
`Categorification.Flag.GammaErratumCheck`). -/
def relationQT' : (r : Rel SRD) → LinDiagram k r.dom r.cod
  | .downupEF i j h μ =>
    if (slCartan m).dot i j = -1 then
      of (crossl SRD i j μ ≫ crossr SRD i j μ) -
        (((((j : ℕ) : ℤ) - ((i : ℕ) : ℤ) : ℤ) : k) • of (𝟙 _))
    else relation (RD := SRD) k (.downupEF i j h μ)
  | .downupFE i j h μ =>
    if (slCartan m).dot i j = -1 then
      of (crossr SRD j i μ ≫ crossl SRD j i μ) -
        (((((i : ℕ) : ℤ) - ((j : ℕ) : ℤ) : ℤ) : k) • of (𝟙 _))
    else relation (RD := SRD) k (.downupFE i j h μ)
  | r => relationQT k m r

/-- The consistent variant `presSignedQT'` of the revised Definition 4.1. -/
def presSignedQT' : Presentation.{w, 0} (psig (slRootDatum m)) k :=
  ((pres0 SRD k).pivotal (inv SRD).toColourDuality).addRels (Rel SRD) Rel.dom Rel.cod
    (relationQT' k m)

/-- The arXiv v1 presentation `presSigned` is the same pivotal base with the relations
`relationQ … qSigned`. -/
theorem presSigned_eq : presSigned k m =
    ((pres0 SRD k).pivotal (inv SRD).toColourDuality).addRels (Rel SRD) Rel.dom Rel.cod
      (relationQ SRD k (qSigned k m)) := rfl

/-! ### Comparison with arXiv v1 -/

variable {m}

/-- The relations modified by [Err]: `downupEF`, `downupFE` with `i · j = -1` and `cycCrossR`,
`cycCrossL` with `j · i = -1`. -/
def IsRevised : Rel SRD → Prop
  | .downupEF i j _ _ => (slCartan m).dot i j = -1
  | .downupFE i j _ _ => (slCartan m).dot i j = -1
  | .cycCrossR j i _ => (slCartan m).dot j i = -1
  | .cycCrossL j i _ => (slCartan m).dot j i = -1
  | _ => False

/-- The relations on which `presSignedQT` and `presSignedQT'` differ: the adjacent `downup`
relations. -/
def IsDownupAdj : Rel SRD → Prop
  | .downupEF i j _ _ => (slCartan m).dot i j = -1
  | .downupFE i j _ _ => (slCartan m).dot i j = -1
  | _ => False

variable {k}

/-- **Only the listed relations change**: away from the adjacent `downup` and crossing-cyclicity
relations, the revised Definition 4.1 has the relations of arXiv v1 Definition 4.1. -/
theorem relationQT_of_not_revised (r : Rel SRD) (h : ¬ IsRevised r) :
    relationQT k m r = relationQ SRD k (qSigned k m) r := by
  cases r with
  | downupEF i j hij μ => exact if_neg h
  | downupFE i j hij μ => exact if_neg h
  | cycCrossR j i μ => exact if_neg h
  | cycCrossL j i μ => exact if_neg h
  | _ => rfl

/-- The consistent variant also only changes the listed relations. -/
theorem relationQT'_of_not_revised (r : Rel SRD) (h : ¬ IsRevised r) :
    relationQT' k m r = relationQ SRD k (qSigned k m) r := by
  cases r with
  | downupEF i j hij μ => exact if_neg h
  | downupFE i j hij μ => exact if_neg h
  | cycCrossR j i μ => exact if_neg h
  | cycCrossL j i μ => exact if_neg h
  | _ => rfl

/-- `presSignedQT'` and `presSignedQT` agree except on the adjacent `downup` relations. -/
theorem relationQT'_eq_relationQT (r : Rel SRD) (h : ¬ IsDownupAdj r) :
    relationQT' k m r = relationQT k m r := by
  cases r with
  | downupEF i j hij μ =>
    have h' : ¬ (slCartan m).dot i j = -1 := h
    exact (if_neg h').trans (if_neg h').symm
  | downupFE i j hij μ =>
    have h' : ¬ (slCartan m).dot i j = -1 := h
    exact (if_neg h').trans (if_neg h').symm
  | _ => rfl

open LinDiagram in
/-- **[Err] p. 98, first (3.13) display**, `i · j = -1`: `crossl i j ≫ crossr i j = (i - j)`. -/
theorem relationQT_downupEF_adj {i j : Fin m} (hij : i ≠ j) (μ : Fin m → ℤ)
    (h : (slCartan m).dot i j = -1) :
    relationQT k m (.downupEF i j hij μ) = of (crossl SRD i j μ ≫ crossr SRD i j μ) -
      (((((i : ℕ) : ℤ) - ((j : ℕ) : ℤ) : ℤ) : k) • of (𝟙 _)) :=
  if_pos h

open LinDiagram in
/-- **[Err] p. 98, second (3.13) display**, `i · j = -1`: `crossr j i ≫ crossl j i = (j - i)` on
`F_i E_j`. -/
theorem relationQT_downupFE_adj {i j : Fin m} (hij : i ≠ j) (μ : Fin m → ℤ)
    (h : (slCartan m).dot i j = -1) :
    relationQT k m (.downupFE i j hij μ) = of (crossr SRD j i μ ≫ crossl SRD j i μ) -
      (((((j : ℕ) : ℤ) - ((i : ℕ) : ℤ) : ℤ) : k) • of (𝟙 _)) :=
  if_pos h

open LinDiagram in
/-- **[Err] p. 97, cyclicity display**, `j · i = -1`: `rotCrossR j i = -rotCrossL j i`. -/
theorem relationQT_cycCrossR_adj (i j : Fin m) (μ : Fin m → ℤ)
    (h : (slCartan m).dot j i = -1) :
    relationQT k m (.cycCrossR j i μ) = of (rotCrossR SRD j i μ) + of (rotCrossL SRD j i μ) :=
  if_pos h

/-- For `j · i = -1` the literal revised definition imposes no further relation (the index
`cycCrossL j i μ` carries the zero relation). -/
theorem relationQT_cycCrossL_adj (i j : Fin m) (μ : Fin m → ℤ)
    (h : (slCartan m).dot j i = -1) :
    relationQT k m (.cycCrossL j i μ) = 0 :=
  if_pos h

open LinDiagram in
/-- The consistent variant, `downupEF`, `i · j = -1`: `crossl i j ≫ crossr i j = (j - i)`. -/
theorem relationQT'_downupEF_adj {i j : Fin m} (hij : i ≠ j) (μ : Fin m → ℤ)
    (h : (slCartan m).dot i j = -1) :
    relationQT' k m (.downupEF i j hij μ) = of (crossl SRD i j μ ≫ crossr SRD i j μ) -
      (((((j : ℕ) : ℤ) - ((i : ℕ) : ℤ) : ℤ) : k) • of (𝟙 _)) :=
  if_pos h

open LinDiagram in
/-- The consistent variant, `downupFE`, `i · j = -1`: `crossr j i ≫ crossl j i = (i - j)`. -/
theorem relationQT'_downupFE_adj {i j : Fin m} (hij : i ≠ j) (μ : Fin m → ℤ)
    (h : (slCartan m).dot i j = -1) :
    relationQT' k m (.downupFE i j hij μ) = of (crossr SRD j i μ ≫ crossl SRD j i μ) -
      (((((i : ℕ) : ℤ) - ((j : ℕ) : ℤ) : ℤ) : k) • of (𝟙 _)) :=
  if_pos h

/-! ### Homogeneity -/

theorem dot_self (c : Fin m) : (slCartan m).dot c c = 2 := by
  rw [slCartan_dot, if_pos rfl]

theorem dot_eq_neg_one_of_ne_zero {c d : Fin m} (h : c ≠ d) (h0 : (slCartan m).dot c d ≠ 0) :
    (slCartan m).dot c d = -1 := by
  rw [slCartan_dot] at h0 ⊢
  rw [if_neg h] at h0 ⊢
  split_ifs at h0 ⊢ with h1
  · rfl
  · exact absurd rfl h0

/-- `Q^τ_{cd}` is weighted homogeneous of degree `-2 c·d` (weights `c·c`, `d·d`). -/
theorem qSigned_isWeightedHomogeneous {c d : Fin m} (h : c ≠ d) :
    (qSigned k m c d).IsWeightedHomogeneous ![(slCartan m).dot c c, (slCartan m).dot d d]
      (-2 * (slCartan m).dot c d) := by
  by_cases h0 : (slCartan m).dot c d = 0
  · rw [qSigned_of_dot_eq_zero h0, h0, mul_zero]
    exact isWeightedHomogeneous_one _ _
  · have hadj := dot_eq_neg_one_of_ne_zero h h0
    rw [qSigned_of_adj hadj, hadj, dot_self, dot_self, ← mem_weightedHomogeneousSubmodule]
    refine zsmul_mem (Submodule.sub_mem _ ?_ ?_) _ <;> rw [mem_weightedHomogeneousSubmodule]
    · convert isWeightedHomogeneous_X k ![(2 : ℤ), 2] 0 using 1
    · convert isWeightedHomogeneous_X k ![(2 : ℤ), 2] 1 using 1

/-- `Q̄^τ_{cd}` is weighted homogeneous of degree `-2 c·d - c·c`. -/
theorem qbar_qSigned_isWeightedHomogeneous {c d : Fin m} (h : c ≠ d) :
    (KLR.qbar (qSigned k m c d)).IsWeightedHomogeneous
      ![(slCartan m).dot c c, (slCartan m).dot d d, (slCartan m).dot c c]
      (-2 * (slCartan m).dot c d - (slCartan m).dot c c) := by
  by_cases h0 : (slCartan m).dot c d = 0
  · rw [qbar_qSigned_of_dot_eq_zero h0]
    exact isWeightedHomogeneous_zero _ _ _
  · have hadj := dot_eq_neg_one_of_ne_zero h h0
    rw [qbar_qSigned_of_adj hadj, hadj, dot_self]
    convert isWeightedHomogeneous_C _ _ using 1

variable (k m)

/-- **arXiv v1 Definition 4.1 is homogeneous** for the degree of Definition 3.1. -/
theorem presSigned_isHomogeneous : (presSigned k m).IsHomogeneous (deg SRD) :=
  presQ_isHomogeneous SRD (qSigned k m) (fun _ _ h => qSigned_isWeightedHomogeneous h)
    (fun _ _ h => qbar_qSigned_isWeightedHomogeneous h)

theorem relationQSigned_mem (r : Rel SRD) :
    ∃ d, relationQ SRD k (qSigned k m) r ∈ HD r.dom r.cod d :=
  relationQ_mem SRD (qSigned k m) (fun _ _ h => qSigned_isWeightedHomogeneous h)
    (fun _ _ h => qbar_qSigned_isWeightedHomogeneous h) r

theorem crosslr_mem (i j : Fin m) (μ : Fin m → ℤ) (s : k) :
    LinDiagram.of (crossl SRD i j μ ≫ crossr SRD i j μ) - s • LinDiagram.of (𝟙 _) ∈
      HD (ob SRD μ [up i, dn j]) (ob SRD μ [up i, dn j]) 0 := by
  refine Submodule.sub_mem _ (LinDiagram.of_mem_homDeg' ?_)
    (Submodule.smul_mem _ _ (LinDiagram.id_mem_homDeg _))
  rw [Diagram.degree_comp, degree_crossl, degree_crossr, add_zero]

theorem crossrl_mem (i j : Fin m) (μ : Fin m → ℤ) (s : k) :
    LinDiagram.of (crossr SRD j i μ ≫ crossl SRD j i μ) - s • LinDiagram.of (𝟙 _) ∈
      HD (ob SRD μ [dn i, up j]) (ob SRD μ [dn i, up j]) 0 := by
  refine Submodule.sub_mem _ (LinDiagram.of_mem_homDeg' ?_)
    (Submodule.smul_mem _ _ (LinDiagram.id_mem_homDeg _))
  rw [Diagram.degree_comp, degree_crossl, degree_crossr, add_zero]

theorem relationQT_mem (r : Rel SRD) : ∃ d, relationQT k m r ∈ HD r.dom r.cod d := by
  by_cases hr : IsRevised r
  · cases r with
    | downupEF i j hij μ =>
      rw [relationQT_downupEF_adj hij μ hr]; exact ⟨0, crosslr_mem k m i j μ _⟩
    | downupFE i j hij μ =>
      rw [relationQT_downupFE_adj hij μ hr]; exact ⟨0, crossrl_mem k m i j μ _⟩
    | cycCrossR j i μ =>
      rw [relationQT_cycCrossR_adj i j μ hr]
      exact ⟨_, Submodule.add_mem _ (LinDiagram.of_mem_homDeg' (degree_rotCrossR j i μ))
        (LinDiagram.of_mem_homDeg' (degree_rotCrossL j i μ))⟩
    | cycCrossL j i μ =>
      rw [relationQT_cycCrossL_adj i j μ hr]; exact ⟨0, Submodule.zero_mem _⟩
    | _ => exact hr.elim
  · rw [relationQT_of_not_revised r hr]; exact relationQSigned_mem k m r

theorem relationQT'_mem (r : Rel SRD) : ∃ d, relationQT' k m r ∈ HD r.dom r.cod d := by
  by_cases hr : IsDownupAdj r
  · cases r with
    | downupEF i j hij μ =>
      rw [relationQT'_downupEF_adj hij μ hr]; exact ⟨0, crosslr_mem k m i j μ _⟩
    | downupFE i j hij μ =>
      rw [relationQT'_downupFE_adj hij μ hr]; exact ⟨0, crossrl_mem k m i j μ _⟩
    | _ => exact hr.elim
  · rw [relationQT'_eq_relationQT r hr]; exact relationQT_mem k m r

/-- **The revised Definition 4.1 is homogeneous** for the degree of Definition 3.1. -/
theorem presSignedQT_isHomogeneous : (presSignedQT k m).IsHomogeneous (deg SRD) :=
  addRels_isHomogeneous SRD _ (relationQT_mem k m)

/-- **The consistent variant is homogeneous** for the degree of Definition 3.1. -/
theorem presSignedQT'_isHomogeneous : (presSignedQT' k m).IsHomogeneous (deg SRD) :=
  addRels_isHomogeneous SRD _ (relationQT'_mem k m)

end Signed

end Categorification.KL3.Diagram
