/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.Relations

/-!
# The presented 2-category `U` of Khovanov–Lauda III and its biadjunctions

M. Khovanov, A. Lauda, *A categorification of quantum `sl(n)`*, arXiv:0807.3250v1, §3.1.1,
Definition 3.1.

`pres RD k` is the presentation of `U` over the commutative ring `k`: the pivotal extension of
the base signature (dots and crossings) adds the four cups and caps and imposes the zigzag
relations (KL III eqs. (3.1), (3.2)); the remaining relations of Definition 3.1 are added with
`Presentation.addRels` (`Relations.lean`). The interchange law is imposed by the library.
`(pres RD k).Presented` is the linear category of 1-morphisms and 2-morphisms of `U` (before
grading shifts, direct sums and the Karoubi envelope), and `(pres RD k).Bicat` is the strict
bicategory `U` with objects the weights.

This is the 2-category `U` of Definition 3.1 without grading shifts `{t}`: KL III's
`Hom_U(x{t}, y{t'})` is the degree `t - t'` part of the morphisms `x ⟶ y` here; the grading is
`deg` (`Categorification.Diagrams.KL3.Basic`). The formal direct sums of Definition 3.1 are not
included.

## Main definitions and results

* `pres RD k`, `U RD k` (its presented bicategory).
* `zigzags`: the zigzag relations hold (eqs. (3.1), (3.2)).
* `strandE RD k i λ = E_{+i} 1_λ` and `strandF RD k i λ = E_{-i} 1_{λ+i_X}` as 1-morphisms of
  `U RD k` (library direction: from the left region to the right region, see
  `Categorification.Diagrams.KL3.Basic`).
* `biadjEF RD k i λ : strandE ⊣⊢ strandF` (KL III (3.1)–(3.2): `1_{λ+i_X} E_{+i} 1_λ` and
  `1_λ E_{-i} 1_{λ+i_X}` are biadjoint), with units and counits the cups and caps
  (`biadjEF_left_unit`, …).
* `biadjColour RD k`: the biadjunctions of all strands, hence of all words (`biadj`).
-/

noncomputable section

namespace Categorification.KL3.Diagram

open CategoryTheory StringDiagrams QuantumGroup UDot Presentation Biadjunction

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : RootDatum C X Y) (k : Type w) [CommRing k]

/-- The base presentation: no relations among dots and crossings alone (all relations of `U`
are added after the pivotal extension). -/
def pres0 : Presentation.{w, max u v} (sig0 RD) k :=
  ⟨PEmpty, PEmpty.elim, PEmpty.elim, fun i => i.elim⟩

/-- **The 2-category `U` of KL III, Definition 3.1**, as a presentation: the pivotal extension
of `pres0` (cups, caps and the zigzag relations (3.1), (3.2)) with the relations `relation`. -/
def pres : Presentation.{w, max u v} (psig RD) k :=
  ((pres0 RD k).pivotal (inv RD).toColourDuality).addRels (Rel RD) Rel.dom Rel.cod (relation (RD := RD) k)

/-- The strict bicategory `U`: objects are the weights `λ ∈ X` (wrapped), 1-morphisms are the
well-formed words of strands, 2-morphisms are the morphisms of `(pres RD k).Presented`. -/
abbrev U : Type v := (pres RD k).Bicat

/-- The zigzag relations (KL III eqs. (3.1), (3.2)) hold in `U`. -/
theorem zigzags : (pres RD k).PivotalZigzags (inv RD).toColourDuality :=
  Presentation.pivotal_addRels_zigzags (inv RD).toColourDuality (pres0 RD k) (Rel RD) _ _ _

/-- The biadjunctions `c ⊣⊢ c*` of all strands `c`, at every placement, given by the cups and
caps. -/
abbrev biadjColour : ColourBiadjunctions (pres RD k) (inv RD).toColourDuality.pivotal :=
  Presentation.pivotalBiadj (inv RD) (pres RD k) (zigzags RD k)

/-- The object `λ` of `U`. -/
abbrev wtObj (lam : X) : U RD k := ⟨lam⟩

/-- The 1-morphism `E_{+i} 1_λ = 1_{λ+i_X} E_i 1_λ` (in the library's direction, from its left
region `λ + i_X` to its right region `λ`). -/
abbrev strandE (i : I) (lam : X) : (⟨sh RD (up i) + lam⟩ : U RD k) ⟶ ⟨lam⟩ :=
  (pres RD k).colourHom (⟨up i, lam⟩ : Col I X)

/-- The 1-morphism `E_{-i} 1_{λ+i_X} = 1_λ F_i 1_{λ+i_X}`: the dual of `strandE`. -/
abbrev strandF (i : I) (lam : X) : (⟨lam⟩ : U RD k) ⟶ ⟨sh RD (up i) + lam⟩ :=
  (pres RD k).dualHom (inv RD).toColourDuality.pivotal (strandE RD k i lam)

theorem strandF_obj (i : I) (lam : X) :
    (strandF RD k i lam).obj = ⟨lam, [⟨dn i, sh RD (up i) + lam⟩]⟩ := rfl

/-- **KL III (3.1)–(3.2)**: `1_{λ+i_X} E_{+i} 1_λ` and `1_λ E_{-i} 1_{λ+i_X}` are biadjoint. The
adjunction `E ⊣ F` has unit the cup `1 → E F` and counit the cap `F E → 1`; the adjunction
`F ⊣ E` has unit the cup `1 → F E` and counit the cap `E F → 1` (`biadjEF_left_unit`, …). -/
abbrev biadjEF (i : I) (lam : X) : strandE RD k i lam ⊣⊢ strandF RD k i lam :=
  biadjColour RD k (strandE RD k i lam) ⟨up i, lam⟩ rfl

theorem biadjEF_left_unit (i : I) (lam : X) :
    (biadjEF RD k i lam).left.unit =
      (pres RD k).diag (Pivotal.cupD (inv RD).toColourDuality (⟨up i, lam⟩ : Col I X)) := rfl

theorem biadjEF_left_counit (i : I) (lam : X) :
    (biadjEF RD k i lam).left.counit =
      (pres RD k).diag (Pivotal.capD (inv RD).toColourDuality (⟨up i, lam⟩ : Col I X)) := rfl

/-- Every 1-morphism of `U` is biadjoint to its dual word, by nested cups and caps. -/
abbrev biadjWord {l m : U RD k} (x : l ⟶ m) :
    x ⊣⊢ (pres RD k).dualHom (inv RD).toColourDuality.pivotal x :=
  biadj (biadjColour RD k) x

end Categorification.KL3.Diagram
