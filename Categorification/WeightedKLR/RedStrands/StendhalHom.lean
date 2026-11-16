/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.WeightedKLR.RedStrands.StendhalCrossing
import Categorification.WeightedKLR.RedStrands.Reduced

/-!
# The map from Stendhal diagrams to the weighted KLR algebra of `Γ_λ`

B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4, proof of
Theorem 3.5: the homomorphism from Webster's algebra `T̃^λ` of Stendhal diagrams to the reduced
weighted KLR algebra of the Crawley-Boevey graph `Γ_λ` (`WeightedGraph.crawleyBoeveyIn`, old
edges of weight `0`, new weights `ϖ_1 < ⋯ < ϖ_ℓ`), sending the red strands to the ghosts of the
`0`-strand.

## The target algebra

Distinct Stendhal sequences can have loadings in the same chamber (exchanging two neighbouring
black strands of colours not joined by an edge crosses no hyperplane). As in Webster's
Proposition 2.14 (`SpacedAlgebra`), the weighted KLR algebra on the family of loadings
`(stFull i)_i`, one idempotent per red-ordered sequence `i`, is the corner of the matrix algebra
over the gallery algebra cut out by the diagonal idempotent `diag(e(stFull i))_i`
(`chamberMatIdem`, `ChamberAlgebra`). Its polynomial representation (`chamberRep`) is faithful.

## The map

The generators of the KLR algebra `R(ν + {λ_1, …, λ_ℓ})` for the polynomials
`stQ a b = P₂(b, a) · P₂(a, b)(v, u)` (`P₂ = stP`) go to:
* `e(i)` to the idempotent of `stFull i` if the red strands of `i` read `λ_1, …, λ_ℓ`, and to
  `0` otherwise;
* the dot on the strand at position `a` to the dot on the corresponding strand of `ν̃`: a black
  strand, or the `0`-strand for a red strand;
* the crossing `ψ_n` to `stCross` (`Stendhal.galleryRep_stCross`), rescaled by
  `(-1) ^ α_a^∨(λ_r)` for a black `a`-strand crossing over to the left of `λ_r`.

The relations are checked in the faithful polynomial representation: renaming the variables of
the KLR polynomial representation (KL I, Proposition 2.3, for `P = stP`) to the strands of `ν̃`
intertwines it with the polynomial representation of `ChamberAlgebra` (`chamberOp_stGenMat`).
Since every operator of the gallery algebra commutes with the dot on the `0`-strand, this
determines the operators.

## Main definitions and results

* `chamberMatIdem`, `ChamberAlgebra`, `chamberRep`, `chamberRep_injective`: the weighted KLR
  algebra on a family of chambers and its faithful polynomial representation.
* `Stendhal.stQ`, `Stendhal.stKLRHom`: the homomorphism from the KLR algebra of `stQ`.
-/

namespace Categorification.WeightedKLR

open Equiv MvPolynomial FullChamber GalleryAlgebra

section ChamberMatrix

variable {J : Type*} [DecidableEq J] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k] {Δ : WeightedGraph J 𝕜 k} {ν : J →₀ ℕ}
  {ι : Type*} [Fintype ι] [DecidableEq ι]

variable (k) in
/-- The diagonal idempotent `diag(e(F i))_i` of the matrix algebra over the gallery algebra, for
a family `F` of chambers. -/
noncomputable def chamberMatIdem (F : ι → FullChamber Δ ν) : Matrix ι ι (GalleryAlgebra k Δ ν) :=
  Matrix.diagonal fun i => e (F i)

theorem isIdempotentElem_chamberMatIdem (F : ι → FullChamber Δ ν) :
    IsIdempotentElem (chamberMatIdem k F) := by
  rw [IsIdempotentElem, chamberMatIdem, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  simp [e_mul_e]

variable (k) in
/-- The weighted KLR algebra on a family `F` of chambers, one idempotent per member of the
family: the corner of `Matrix ι ι A` (`A` the gallery algebra) at `chamberMatIdem F`. Its `(j, i)`
entry lies in `e(F j) A e(F i)`. -/
abbrev ChamberAlgebra (F : ι → FullChamber Δ ν) : Type _ :=
  (isIdempotentElem_chamberMatIdem (k := k) F).Corner

variable {F : ι → FullChamber Δ ν}

theorem galleryRep_eq_of_mul_e (hΓ : Δ.PSymm) {x : GalleryAlgebra k Δ ν}
    {C : FullChamber Δ ν} (hx : x * e C = x) (v : FullChamber Δ ν → PolyRing ν k) :
    galleryRep k hΓ x v = galleryRep k hΓ x (Pi.single C (v C)) := by
  conv_lhs => rw [← hx]
  rw [map_mul, galleryRep_e, Module.End.mul_apply, blk_apply, LinearMap.id_apply]

theorem galleryRep_eq_of_e_mul (hΓ : Δ.PSymm) {x : GalleryAlgebra k Δ ν}
    {C : FullChamber Δ ν} (hx : e C * x = x) (v : FullChamber Δ ν → PolyRing ν k) :
    galleryRep k hΓ x v = Pi.single C (galleryRep k hΓ x v C) := by
  conv_lhs => rw [← hx]
  rw [map_mul, galleryRep_e, Module.End.mul_apply, blk_apply, LinearMap.id_apply]

theorem ChamberAlgebra.e_mul (x : ChamberAlgebra k F) (j i : ι) :
    e (F j) * x.1 j i = x.1 j i := by
  have h := ((Subsemigroup.mem_corner_iff (isIdempotentElem_chamberMatIdem F)).1 x.2).1
  have := congrFun (congrFun h j) i
  simpa [chamberMatIdem, Matrix.diagonal_mul] using this

theorem ChamberAlgebra.mul_e (x : ChamberAlgebra k F) (j i : ι) :
    x.1 j i * e (F i) = x.1 j i := by
  have h := ((Subsemigroup.mem_corner_iff (isIdempotentElem_chamberMatIdem F)).1 x.2).2
  have := congrFun (congrFun h j) i
  simpa [chamberMatIdem, Matrix.mul_diagonal] using this

variable (k F) in
/-- The polynomial representation of the matrix algebra over the gallery algebra on
`ι → k[y_t]`: the entry `c j i` acts from the `i`-th copy, placed in the copy of `F i`, to the
`j`-th copy, read off at the copy of `F j`. -/
noncomputable def chamberOp (hΓ : Δ.PSymm) (c : Matrix ι ι (GalleryAlgebra k Δ ν)) :
    Module.End k (ι → PolyRing ν k) :=
  LinearMap.pi fun j => ∑ i,
    (LinearMap.proj (R := k) (φ := fun _ : FullChamber Δ ν => PolyRing ν k) (F j)) ∘ₗ
      galleryRep k hΓ (c j i) ∘ₗ
      LinearMap.single k (fun _ : FullChamber Δ ν => PolyRing ν k) (F i) ∘ₗ
      LinearMap.proj (R := k) (φ := fun _ : ι => PolyRing ν k) i

omit [DecidableEq ι] in
theorem chamberOp_apply (hΓ : Δ.PSymm) (c : Matrix ι ι (GalleryAlgebra k Δ ν))
    (g : ι → PolyRing ν k) (j : ι) :
    chamberOp k F hΓ c g j = ∑ i, galleryRep k hΓ (c j i) (Pi.single (F i) (g i)) (F j) := by
  simp [chamberOp, LinearMap.sum_apply]

theorem chamberOp_single (hΓ : Δ.PSymm) (c : Matrix ι ι (GalleryAlgebra k Δ ν)) (i : ι)
    (p : PolyRing ν k) (j : ι) :
    chamberOp k F hΓ c (Pi.single i p) j =
      galleryRep k hΓ (c j i) (Pi.single (F i) p) (F j) := by
  rw [chamberOp_apply, Finset.sum_eq_single i]
  · rw [Pi.single_eq_same]
  · intro i' _ hi'
    rw [Pi.single_eq_of_ne hi', Pi.single_zero, map_zero, Pi.zero_apply]
  · intro h
    exact absurd (Finset.mem_univ i) h

omit [DecidableEq ι] in
theorem chamberOp_add (hΓ : Δ.PSymm) (c d : Matrix ι ι (GalleryAlgebra k Δ ν)) :
    chamberOp k F hΓ (c + d) = chamberOp k F hΓ c + chamberOp k F hΓ d := by
  refine LinearMap.ext fun g => funext fun j => ?_
  simp only [chamberOp_apply, LinearMap.add_apply, Pi.add_apply, Matrix.add_apply, map_add,
    ← Finset.sum_add_distrib]

omit [DecidableEq ι] in
theorem chamberOp_smul (hΓ : Δ.PSymm) (a : k) (c : Matrix ι ι (GalleryAlgebra k Δ ν)) :
    chamberOp k F hΓ (a • c) = a • chamberOp k F hΓ c := by
  refine LinearMap.ext fun g => funext fun j => ?_
  simp only [chamberOp_apply, LinearMap.smul_apply, Pi.smul_apply, Matrix.smul_apply, map_smul,
    Finset.smul_sum]

theorem chamberOp_chamberMatIdem (hΓ : Δ.PSymm) : chamberOp k F hΓ (chamberMatIdem k F) = 1 := by
  refine LinearMap.ext fun g => funext fun j => ?_
  rw [chamberOp_apply, Finset.sum_eq_single j]
  · simp [chamberMatIdem, galleryRep_e, blk_apply]
  · intro i _ hij
    simp [chamberMatIdem, Matrix.diagonal_apply_ne _ (Ne.symm hij)]
  · intro h
    exact absurd (Finset.mem_univ j) h

omit [DecidableEq ι] in
theorem chamberOp_mul (hΓ : Δ.PSymm) {c : Matrix ι ι (GalleryAlgebra k Δ ν)}
    (hc : ∀ j i, c j i * e (F i) = c j i) (d : Matrix ι ι (GalleryAlgebra k Δ ν)) :
    chamberOp k F hΓ (c * d) = chamberOp k F hΓ c * chamberOp k F hΓ d := by
  refine LinearMap.ext fun g => funext fun l => ?_
  have key : ∀ j, galleryRep k hΓ (c l j) (Pi.single (F j) (chamberOp k F hΓ d g j)) =
      ∑ i, galleryRep k hΓ (c l j) (galleryRep k hΓ (d j i) (Pi.single (F i) (g i))) := by
    intro j
    rw [← map_sum, galleryRep_eq_of_mul_e hΓ (hc l j)
      (∑ i, galleryRep k hΓ (d j i) (Pi.single (F i) (g i))),
      Finset.sum_apply, chamberOp_apply]
  rw [Module.End.mul_apply, chamberOp_apply, chamberOp_apply]
  simp only [key, Matrix.mul_apply, map_sum, map_mul, LinearMap.sum_apply, Finset.sum_apply,
    Module.End.mul_apply]
  exact Finset.sum_comm

theorem chamberOp_sandwich (hΓ : Δ.PSymm) (c : Matrix ι ι (GalleryAlgebra k Δ ν)) :
    chamberOp k F hΓ (chamberMatIdem k F * c * chamberMatIdem k F) = chamberOp k F hΓ c := by
  refine LinearMap.ext fun g => funext fun j => ?_
  rw [chamberOp_apply, chamberOp_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [chamberMatIdem, Matrix.mul_diagonal, Matrix.diagonal_mul, galleryRep_e, blk_apply]

theorem chamberOp_diagonal (hΓ : Δ.PSymm) (d : ι → GalleryAlgebra k Δ ν)
    (g : ι → PolyRing ν k) (j : ι) :
    chamberOp k F hΓ (Matrix.diagonal d) g j =
      galleryRep k hΓ (d j) (Pi.single (F j) (g j)) (F j) := by
  rw [chamberOp_apply, Finset.sum_eq_single j]
  · rw [Matrix.diagonal_apply_eq]
  · intro i _ hij
    rw [Matrix.diagonal_apply_ne _ (Ne.symm hij), map_zero, LinearMap.zero_apply, Pi.zero_apply]
  · intro h
    exact absurd (Finset.mem_univ j) h

variable (k F) in
/-- The polynomial representation of the weighted KLR algebra on a family of chambers. -/
noncomputable def chamberRep (hΓ : Δ.PSymm) :
    ChamberAlgebra k F →ₐ[k] Module.End k (ι → PolyRing ν k) :=
  AlgHom.ofLinearMap
    { toFun := fun x => chamberOp k F hΓ x.1
      map_add' := fun x y => chamberOp_add hΓ x.1 y.1
      map_smul' := fun a x => chamberOp_smul hΓ a x.1 }
    (chamberOp_chamberMatIdem hΓ)
    (fun x y => chamberOp_mul hΓ (ChamberAlgebra.mul_e x) y.1)

theorem chamberRep_apply (hΓ : Δ.PSymm) (x : ChamberAlgebra k F) :
    chamberRep k F hΓ x = chamberOp k F hΓ x.1 := rfl

variable (k F) in
/-- The element `diag(e(F)) c diag(e(F))` of the corner. -/
noncomputable def chamberElt (c : Matrix ι ι (GalleryAlgebra k Δ ν)) : ChamberAlgebra k F :=
  ⟨chamberMatIdem k F * c * chamberMatIdem k F,
    (Subsemigroup.mem_corner_iff (isIdempotentElem_chamberMatIdem F)).2
      ⟨by rw [← mul_assoc, ← mul_assoc, (isIdempotentElem_chamberMatIdem F).eq],
        by rw [mul_assoc, (isIdempotentElem_chamberMatIdem F).eq]⟩⟩

theorem chamberRep_chamberElt (hΓ : Δ.PSymm) (c : Matrix ι ι (GalleryAlgebra k Δ ν)) :
    chamberRep k F hΓ (chamberElt k F c) = chamberOp k F hΓ c :=
  chamberOp_sandwich hΓ c

/-- The polynomial representation of the weighted KLR algebra on a family of chambers is
faithful, under the hypotheses of the basis theorem. -/
theorem chamberRep_injective (hD : Δ.Dagger) (hZ : Δ.NoZeroLoops) (hΓ : Δ.PSymm)
    (hW : ∀ w : Wall Δ ν, IsRegular (w.factor (k := k)))
    (hL : ∀ (Q : MvPolynomial (Fin 2) k) (a b : Strand ν), Δ.loop a.1 = some Q → a ≠ b →
      a.1 = b.1 → IsRegular (loopFactor Q a b)) :
    Function.Injective (chamberRep k F hΓ) := by
  intro x y hxy
  have h' : chamberOp k F hΓ x.1 = chamberOp k F hΓ y.1 := hxy
  apply Subtype.ext
  funext j i
  refine galleryRep_injective hD hZ hΓ hW hL ?_
  refine LinearMap.ext fun v => ?_
  rw [galleryRep_eq_of_e_mul hΓ (ChamberAlgebra.e_mul x j i),
    galleryRep_eq_of_mul_e hΓ (ChamberAlgebra.mul_e x j i),
    galleryRep_eq_of_e_mul hΓ (ChamberAlgebra.e_mul y j i) v,
    galleryRep_eq_of_mul_e hΓ (ChamberAlgebra.mul_e y j i),
    ← chamberOp_single, ← chamberOp_single, h']

/-- Multiplication by `X s` in every component. -/
noncomputable def mulXOp (s : Strand ν) : Module.End k (ι → PolyRing ν k) :=
  LinearMap.pi fun j => LinearMap.mulLeft k (X s) ∘ₗ LinearMap.proj j

omit [DecidableEq J] [Fintype ι] [DecidableEq ι] in
@[simp] theorem mulXOp_apply (s : Strand ν) (g : ι → PolyRing ν k) (j : ι) :
    mulXOp (k := k) s g j = X s * g j := rfl

omit [DecidableEq ι] in
/-- **The dot on a strand alone in its colour commutes with every operator** of the polynomial
representation of the matrix algebra (`GalleryAlgebra.commute_poly_X`). -/
theorem chamberOp_commute_mulXOp {s₀ : Strand ν} (h₀ : ν s₀.1 = 1) (hΓ : Δ.PSymm)
    (c : Matrix ι ι (GalleryAlgebra k Δ ν)) :
    Commute (chamberOp k F hΓ c) (mulXOp s₀) := by
  refine LinearMap.ext fun g => funext fun j => ?_
  have hd : ∀ (x : GalleryAlgebra k Δ ν) (v : FullChamber Δ ν → PolyRing ν k),
      galleryRep k hΓ x (fun C => X s₀ * v C) = fun C => X s₀ * galleryRep k hΓ x v C := by
    intro x v
    have h := congrArg (fun a => galleryRep k hΓ a v) (commute_poly_X h₀ x).eq
    simp only [map_mul, Module.End.mul_apply, galleryRep_poly] at h
    exact h.symm
  simp only [Module.End.mul_apply, chamberOp_apply, mulXOp_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : (Pi.single (F i) (X s₀ * g i) : FullChamber Δ ν → PolyRing ν k) =
      fun C => X s₀ * (Pi.single (F i) (g i) : FullChamber Δ ν → PolyRing ν k) C := by
    funext C
    by_cases hC : C = F i
    · subst hC; simp
    · simp [Pi.single_eq_of_ne hC]
  rw [this, hd]

end ChamberMatrix

end Categorification.WeightedKLR

namespace Categorification

open MvPolynomial Equiv

/-- Renaming the variables commutes with the divided difference `∂_{ab}` when the renaming
commutes with the transposition of `a` and `b`; it need not be injective. -/
theorem rename_ddiff_of_comm {k σ τ : Type*} [CommRing k] [DecidableEq σ] [DecidableEq τ]
    {φ : σ → τ} {a b : σ} (hab : φ a ≠ φ b) (hc : ∀ c, φ (swap a b c) = swap (φ a) (φ b) (φ c))
    (f : MvPolynomial σ k) : rename φ (ddiff a b f) = ddiff (φ a) (φ b) (rename φ f) := by
  have hab' : a ≠ b := fun e => hab (by rw [e])
  symm
  apply ddiff_eq_of_mul hab
  have h := congrArg (rename φ) (ddiff_spec hab' f)
  simp only [map_mul, map_sub, rename_X, rename_rename] at h
  rw [h, rename_rename, show φ ∘ swap a b = swap (φ a) (φ b) ∘ φ from funext hc]

end Categorification

namespace Categorification.Stendhal

open Categorification.WeightedKLR Equiv MvPolynomial FullChamber GalleryAlgebra

section Hom

variable {I : Type} [DecidableEq I] {ℓ : ℕ} {ν : Multiset I}
  {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k]
  {Γ : WeightedGraph I 𝕜 k} {Λ : Fin ℓ → I →₀ ℕ} {ϖ : Fin ℓ → 𝕜}

local notation "μ" => Multiset.toFinsupp (stendhalWeight ℓ ν)
local notation "ν̃" => WeightedGraph.redWeight (Multiset.toFinsupp ν)
local notation "Γλ" => WeightedGraph.crawleyBoeveyIn Γ Λ ϖ
local notation "m" => Multiset.card (stendhalWeight ℓ ν)

noncomputable instance : Fintype (OrdSeq ℓ ν) := Fintype.ofFinite _

variable (Γ Λ) in
/-- The polynomials `Q` of the KLR algebra on the black and red strands for which the
polynomial representation is that of `P₂ = stP`: `stQ a b (u, v) = P₂(b, a)(u, v) ·
P₂(a, b)(v, u)`. Between black strands this is `Γ.klrQ`; for a black `a`-strand and the red
strand `λ_r` it is `(v - u) ^ α_a^∨(λ_r)` (resp. `(u - v) ^ α_a^∨(λ_r)`), which agrees with
Stendhal's `u ^ α_a^∨(λ_r)` (resp. `v ^ α_a^∨(λ_r)`) up to multiples of the variable of the red
strand. -/
noncomputable def stQ (a b : I ⊕ Fin ℓ) : MvPolynomial (Fin 2) k :=
  stP Γ Λ b a * rename ![1, 0] (stP Γ Λ a b)

/-- The renaming of the variables of a sequence to the strands of `ν̃`: a black strand to
itself, a red strand to the `0`-strand. -/
noncomputable def stRen (i : KLR.Seq (stendhalWeight ℓ ν)) :
    MvPolynomial (Fin m) k →ₐ[k] PolyRing ν̃ k :=
  rename fun a => toTilde (i.strandAt a)

variable (ℓ ν k) in
/-- The renaming on the components of red-ordered sequences. -/
noncomputable def stRenOp :
    KLR.PolyRep.Pol k (stendhalWeight ℓ ν) →ₗ[k] (OrdSeq ℓ ν → PolyRing ν̃ k) :=
  LinearMap.pi fun j => (stRen j.1).toLinearMap ∘ₗ LinearMap.proj j.1

@[simp] theorem stRenOp_apply (g : KLR.PolyRep.Pol k (stendhalWeight ℓ ν)) (j : OrdSeq ℓ ν) :
    stRenOp ℓ ν k g j = stRen j.1 (g j.1) := rfl

theorem toTilde_strandAt_ne {i : KLR.Seq (stendhalWeight ℓ ν)} {a b : Fin m}
    (hb : (i.1 b).isLeft) (hab : a ≠ b) : toTilde (i.strandAt a) ≠ toTilde (i.strandAt b) :=
  fun e => hab (i.strandAt_injective (eq_of_toTilde_eq hb e))

omit [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- **The crossings in the two polynomial representations**: renaming intertwines the KLR
crossing for `P₂ = stP` (KL I, §2.3) with `stCrossOp`. -/
theorem stCrossOp_stRen (t : KLR.Seq (stendhalWeight ℓ ν)) (n : ℕ) (h : n + 1 < m)
    (g : MvPolynomial (Fin m) k) :
    stCrossOp k Γ Λ t n h (stRen t g) =
      stRen (TypeA.sadj m n • t) (KLR.PolyRep.crossComp (stP Γ Λ) n h t g) := by
  by_cases hc : t.1 ⟨n, by omega⟩ = t.1 ⟨n + 1, h⟩
  · have hu : (t.1 ⟨n, by omega⟩).isLeft := isLeft_of_eq h hc
    have hv : (t.1 ⟨n + 1, h⟩).isLeft := hc ▸ hu
    have hne : (⟨n, by omega⟩ : Fin m) ≠ ⟨n + 1, h⟩ := by simp [Fin.ext_iff]
    have e1 : stCrossOp k Γ Λ t n h = ddiff (toTilde (t.strandAt ⟨n, by omega⟩))
        (toTilde (t.strandAt ⟨n + 1, h⟩)) := by simp only [stCrossOp, hc, ↓reduceIte]
    have e2 : KLR.PolyRep.crossComp (stP Γ Λ) n h t = ddiff ⟨n, by omega⟩ ⟨n + 1, h⟩ := by
      simp only [KLR.PolyRep.crossComp, KLR.Seq.lbl, hc, ↓reduceIte]
    rw [e1, e2, KLR.Seq.sadj_smul_of_eq t h hc]
    symm
    refine rename_ddiff_of_comm (φ := fun a => toTilde (t.strandAt a))
      (toTilde_strandAt_ne hv hne) (fun c => ?_) g
    by_cases h1 : c = ⟨n, by omega⟩
    · subst h1; simp
    by_cases h2 : c = ⟨n + 1, h⟩
    · subst h2; simp
    rw [swap_apply_of_ne_of_ne h1 h2, swap_apply_of_ne_of_ne
      (toTilde_strandAt_ne hu h1) (toTilde_strandAt_ne hv h2)]
  · have hσ := KLR.Seq.lt_sadj_iff t h hc
    have hsm : ∀ a, (TypeA.sadj m n • t).strandAt (TypeA.sadj m n a) = t.strandAt a :=
      KLR.Seq.strandAt_smul t _ hσ
    simp only [stCrossOp, KLR.PolyRep.crossComp, KLR.Seq.lbl, hc, ↓reduceIte, stRen,
      LinearMap.mulLeft_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_mul,
      rename_rename]
    congr 1
    · refine congrArg (fun φ => rename φ _) (funext fun c => ?_)
      fin_cases c
      · simp [← hsm ⟨n + 1, h⟩, TypeA.sadj_apply_right h]
      · simp [← hsm ⟨n, by omega⟩, TypeA.sadj_apply_left h]
    · exact congrArg (fun φ => rename φ g) (funext fun c => congrArg toTilde (hsm c).symm)

omit [DecidableEq I] in
set_option linter.unusedSimpArgs false in
/-- Exchanging two neighbouring strands, one of them black, keeps the red strands in order. -/
theorem isRedOrdered_sadj {i : KLR.Seq (stendhalWeight ℓ ν)} (hi : IsRedOrdered i) {n : ℕ}
    (h : n + 1 < m) (hb : (i.1 ⟨n, by omega⟩).isLeft ∨ (i.1 ⟨n + 1, h⟩).isLeft) :
    IsRedOrdered (TypeA.sadj m n • i) := by
  have hs : TypeA.sadj m n = swap ⟨n, by omega⟩ ⟨n + 1, h⟩ := by
    simp only [TypeA.sadj, h, ↓reduceDIte]
  have hs' : (TypeA.sadj m n).symm = TypeA.sadj m n := by
    rw [← Perm.inv_def]
    exact inv_eq_of_mul_eq_one_left (TypeA.sadj_mul_self m n)
  intro a b r r' hab ha hb'
  simp only [KLR.Seq.lbl, KLR.Seq.smul_apply] at ha hb'
  rw [hs', hs] at ha hb'
  have key : swap (⟨n, by omega⟩ : Fin m) ⟨n + 1, h⟩ a < swap ⟨n, by omega⟩ ⟨n + 1, h⟩ b ∨
      (a = ⟨n, by omega⟩ ∧ b = ⟨n + 1, h⟩) := by
    rw [Fin.lt_def] at hab
    simp only [swap_apply_def, Fin.lt_def, Fin.ext_iff]
    split_ifs <;> (try simp only [Fin.ext_iff, Fin.val_mk] at *) <;> omega
  rcases key with key | ⟨h1, h2⟩
  · exact hi _ _ r r' key ha hb'
  · rw [h1, swap_apply_left] at ha
    rw [h2, swap_apply_right] at hb'
    rcases hb with hb | hb
    · rw [hb'] at hb; simp at hb
    · rw [ha] at hb; simp at hb

omit [DecidableEq I] in
theorem sadj_smul_sadj_smul (t : KLR.Seq (stendhalWeight ℓ ν)) (n : ℕ) :
    TypeA.sadj m n • TypeA.sadj m n • t = t := by
  rw [smul_smul, TypeA.sadj_mul_self, one_smul]

variable (k Λ) in
/-- The images of the generators of the KLR algebra `R(ν + {λ_1, …, λ_ℓ})` in the matrix
algebra over the gallery algebra of `Γ_λ`: `e(i)` to `e(stFull i)` on the diagonal if the red
strands of `i` are in order (and to `0` otherwise), the dot on the strand at position `a` to the
dot on the corresponding strand of `ν̃` (the `0`-strand for a red strand), and the crossing `ψ_n`
to the matrix of the crossings `stCross`. -/
noncomputable def stGenMat (hϖ : StrictMono ϖ) (hw0 : ∀ e, Γ.weight e = 0) :
    KLR.Gen (stendhalWeight ℓ ν) → Matrix (OrdSeq ℓ ν) (OrdSeq ℓ ν) (GalleryAlgebra k Γλ ν̃)
  | .idem i => Matrix.diagonal fun j => if j.1 = i then e (stFull Λ hϖ hw0 j) else 0
  | .dot a => Matrix.diagonal fun j => poly (X (toTilde (j.1.strandAt a)))
  | .cross n => if h : n + 1 < m then
      Matrix.of fun j i => if j.1 = TypeA.sadj m n • i.1 then stCross k Λ hϖ hw0 i n h else 0
    else 0

/-- **The generators in the two polynomial representations**: renaming intertwines the KLR
polynomial representation for `P₂ = stP` (KL I, Proposition 2.3) with the polynomial
representation of the images `stGenMat` of the generators. -/
theorem chamberOp_stGenMat (hD : Γ.Dagger) (hE : ∀ e, Γ.head e ≠ Γ.tail e)
    (hl : ∀ c, Γ.loop c = none) (hϖ : StrictMono ϖ) (hw0 : ∀ e, Γ.weight e = 0)
    (g : KLR.Gen (stendhalWeight ℓ ν)) (f : KLR.PolyRep.Pol k (stendhalWeight ℓ ν))
    (j : OrdSeq ℓ ν) :
    chamberOp k (stFull Λ hϖ hw0) (WeightedGraph.crawleyBoeveyIn_psymm (psymm_of_loop hl))
        (stGenMat k Λ hϖ hw0 g) (stRenOp ℓ ν k f) j =
      stRen j.1 (KLR.PolyRep.genOp _ (stP Γ Λ) g f j.1) := by
  cases g with
  | idem i =>
    simp only [stGenMat, chamberOp_diagonal, KLR.PolyRep.genOp, KLR.PolyRep.opE_apply]
    by_cases hj : j.1 = i
    · subst hj
      simp [galleryRep_e, blk_apply]
    · simp [hj]
  | dot a =>
    simp [stGenMat, chamberOp_diagonal, KLR.PolyRep.genOp, galleryRep_poly, stRen]
  | cross n =>
    by_cases h : n + 1 < m
    · rw [KLR.PolyRep.genOp, KLR.PolyRep.opΨ_apply _ _ h, chamberOp_apply]
      by_cases ht : IsRedOrdered (TypeA.sadj m n • j.1)
      · rw [Finset.sum_eq_single ⟨TypeA.sadj m n • j.1, ht⟩]
        · have hj : (⟨TypeA.sadj m n • (TypeA.sadj m n • j.1), by
              rw [sadj_smul_sadj_smul]; exact j.2⟩ : OrdSeq ℓ ν) = j :=
            Subtype.ext (sadj_smul_sadj_smul _ _)
          simp only [stGenMat, h, ↓reduceDIte, Matrix.of_apply, sadj_smul_sadj_smul,
            ↓reduceIte]
          rw [galleryRep_stCross hD hE hl hϖ hw0 _ n h, blk_apply, hj, Pi.single_eq_same,
            Pi.single_eq_same, stRenOp_apply, stCrossOp_stRen]
          exact congrArg (fun x => stRen x ((KLR.PolyRep.crossComp (stP Γ Λ) n h
            (TypeA.sadj m n • j.1)) (f (TypeA.sadj m n • j.1)))) (sadj_smul_sadj_smul j.1 n)
          exact (sadj_smul_sadj_smul j.1 n).symm ▸ j.2
        · intro i _ hi
          have hz : stGenMat k Λ hϖ hw0 (.cross n) j i = 0 := by
            simp only [stGenMat, h, ↓reduceDIte, Matrix.of_apply]
            rw [ite_eq_right_iff]
            intro e
            exfalso
            apply hi
            apply Subtype.ext
            show i.1 = TypeA.sadj m n • j.1
            rw [e, sadj_smul_sadj_smul]
          rw [hz, map_zero, LinearMap.zero_apply, Pi.zero_apply]
        · intro hn
          exact absurd (Finset.mem_univ _) hn
      · rw [Finset.sum_eq_zero]
        · have hred : ¬ (j.1.1 ⟨n, by omega⟩).isLeft ∧ ¬ (j.1.1 ⟨n + 1, h⟩).isLeft := by
            by_contra hc
            rw [not_and_or, not_not, not_not] at hc
            exact ht (isRedOrdered_sadj j.2 h hc)
          have hs' : (TypeA.sadj m n).symm = TypeA.sadj m n := by
            rw [← Perm.inv_def]
            exact inv_eq_of_mul_eq_one_left (TypeA.sadj_mul_self m n)
          have e1 : (TypeA.sadj m n • j.1).1 ⟨n, by omega⟩ = j.1.1 ⟨n + 1, h⟩ := by
            rw [KLR.Seq.smul_apply, hs', TypeA.sadj_apply_left h]
          have e2 : (TypeA.sadj m n • j.1).1 ⟨n + 1, h⟩ = j.1.1 ⟨n, by omega⟩ := by
            rw [KLR.Seq.smul_apply, hs', TypeA.sadj_apply_right h]
          obtain ⟨r, hr⟩ : ∃ r, j.1.1 ⟨n, by omega⟩ = .inr r := by
            rcases hx : j.1.1 ⟨n, by omega⟩ with a | r
            · exact absurd (by rw [hx]; rfl) hred.1
            · exact ⟨r, rfl⟩
          obtain ⟨r', hr'⟩ : ∃ r, j.1.1 ⟨n + 1, h⟩ = .inr r := by
            rcases hx : j.1.1 ⟨n + 1, h⟩ with a | r
            · exact absurd (by rw [hx]; rfl) hred.2
            · exact ⟨r, rfl⟩
          have hne : (TypeA.sadj m n • j.1).1 ⟨n, by omega⟩ ≠
              (TypeA.sadj m n • j.1).1 ⟨n + 1, h⟩ := fun hc => by
            have := isLeft_of_eq h hc
            rw [e1, hr'] at this
            simp at this
          simp only [KLR.PolyRep.crossComp, KLR.Seq.lbl, hne, ↓reduceIte]
          simp only [e1, e2, hr, hr', stP, map_zero, LinearMap.comp_apply,
            LinearMap.mulLeft_apply, zero_mul]
        · intro i _
          have hz : stGenMat k Λ hϖ hw0 (.cross n) j i = 0 := by
            simp only [stGenMat, h, ↓reduceDIte, Matrix.of_apply]
            rw [ite_eq_right_iff]
            intro e
            exfalso
            apply ht
            rw [e, sadj_smul_sadj_smul]
            exact i.2
          rw [hz, map_zero, LinearMap.zero_apply, Pi.zero_apply]
    · have h' : m ≤ n + 1 := by omega
      simp only [stGenMat, h, ↓reduceDIte, KLR.PolyRep.genOp, KLR.PolyRep.opΨ_eq_zero _ h',
        LinearMap.zero_apply, Pi.zero_apply, map_zero, chamberOp_apply, Matrix.zero_apply,
        Finset.sum_const_zero]

variable (ν k Λ) in
/-- The images of the generators, on the free algebra. -/
noncomputable def stFreeHom (hϖ : StrictMono ϖ) (hw0 : ∀ e, Γ.weight e = 0) :
    FreeAlgebra k (KLR.Gen (stendhalWeight ℓ ν)) →ₐ[k]
      ChamberAlgebra k (stFull (ν := ν) Λ hϖ hw0) :=
  FreeAlgebra.lift k fun g => chamberElt k _ (stGenMat k Λ hϖ hw0 g)

theorem stFreeHom_ι (hϖ : StrictMono ϖ) (hw0 : ∀ e, Γ.weight e = 0)
    (g : KLR.Gen (stendhalWeight ℓ ν)) :
    stFreeHom ν k Λ hϖ hw0 (FreeAlgebra.ι k g) = chamberElt k _ (stGenMat k Λ hϖ hw0 g) :=
  FreeAlgebra.lift_ι_apply _ _

theorem chamberRep_stFreeHom (hD : Γ.Dagger) (hE : ∀ e, Γ.head e ≠ Γ.tail e)
    (hl : ∀ c, Γ.loop c = none) (hϖ : StrictMono ϖ) (hw0 : ∀ e, Γ.weight e = 0)
    (x : FreeAlgebra k (KLR.Gen (stendhalWeight ℓ ν))) :
    chamberRep k (stFull Λ hϖ hw0) (WeightedGraph.crawleyBoeveyIn_psymm (psymm_of_loop hl))
        (stFreeHom ν k Λ hϖ hw0 x) ∘ₗ stRenOp ℓ ν k =
      stRenOp ℓ ν k ∘ₗ KLR.PolyRep.freeRep _ (stP Γ Λ) x := by
  induction x using FreeAlgebra.induction with
  | grade0 r =>
    simp only [AlgHom.commutes, Module.algebraMap_end_eq_smul_id, LinearMap.smul_comp,
      LinearMap.comp_smul, LinearMap.id_comp, LinearMap.comp_id]
  | grade1 g =>
    refine LinearMap.ext fun f => funext fun j => ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, stFreeHom_ι,
      chamberRep_chamberElt, chamberOp_stGenMat hD hE hl, stRenOp_apply,
      KLR.PolyRep.freeRep, FreeAlgebra.lift_ι_apply]
  | mul a b ha hb =>
    rw [map_mul, map_mul, Module.End.mul_eq_comp, LinearMap.comp_assoc,
      hb, ← LinearMap.comp_assoc, ha, LinearMap.comp_assoc, map_mul]
    rfl
  | add a b ha hb =>
    simp only [map_add, LinearMap.add_comp, LinearMap.comp_add, ha, hb]

theorem stRenOp_single (j : OrdSeq ℓ ν) (q : MvPolynomial (Fin m) k) :
    stRenOp ℓ ν k (Pi.single j.1 q) = Pi.single j (stRen j.1 q) := by
  funext j'
  by_cases hj : j' = j
  · subst hj
    simp
  · rw [stRenOp_apply, Pi.single_eq_of_ne hj, Pi.single_eq_of_ne (fun e => hj (Subtype.ext e)),
      map_zero]

/-- An operator commuting with the dot on the `0`-strand is determined by its composite with
the renaming: the variables of the black strands come from the KLR polynomial representation,
and the variable of the `0`-strand acts through the commuting dot. -/
theorem eq_of_comp_stRenOp {A B : Module.End k (OrdSeq ℓ ν → PolyRing ν̃ k)}
    (hA : Commute A (mulXOp (GalleryAlgebra.zeroStrand (Multiset.toFinsupp ν))))
    (hB : Commute B (mulXOp (GalleryAlgebra.zeroStrand (Multiset.toFinsupp ν))))
    (h : A ∘ₗ stRenOp ℓ ν k = B ∘ₗ stRenOp ℓ ν k) : A = B := by
  have key : ∀ (j : OrdSeq ℓ ν) (p : PolyRing ν̃ k) (q : MvPolynomial (Fin m) k),
      A (Pi.single j (p * stRen j.1 q)) = B (Pi.single j (p * stRen j.1 q)) := by
    intro j p
    induction p using MvPolynomial.induction_on with
    | C c =>
      intro q
      have hc : C c * stRen j.1 q = stRen j.1 (C c * q) := by
        rw [map_mul, stRen, rename_C]
      rw [hc, ← stRenOp_single]
      exact LinearMap.congr_fun h _
    | add p p' hp hp' =>
      intro q
      rw [add_mul, Pi.single_add, map_add, map_add, hp, hp']
    | mul_X p s hp =>
      intro q
      by_cases hs : s = GalleryAlgebra.zeroStrand (Multiset.toFinsupp ν)
      · subst hs
        have hm : (Pi.single j (p * X (GalleryAlgebra.zeroStrand (Multiset.toFinsupp ν)) *
            stRen j.1 q) : OrdSeq ℓ ν → PolyRing ν̃ k) =
            mulXOp (GalleryAlgebra.zeroStrand (Multiset.toFinsupp ν))
              (Pi.single j (p * stRen j.1 q)) := by
          funext j'
          by_cases hj : j' = j
          · subst hj
            simp only [Pi.single_eq_same, mulXOp_apply]
            ring
          · simp [Pi.single_eq_of_ne hj]
        rw [hm, ← Module.End.mul_apply, hA.eq, Module.End.mul_apply, hp,
          ← Module.End.mul_apply, ← hB.eq, Module.End.mul_apply]
      · obtain ⟨s', hs'⟩ := exists_ofTilde_of_ne hs
        have hX : (X s : PolyRing ν̃ k) = stRen j.1 (X (j.1.posOf s')) := by
          rw [stRen, rename_X, KLR.Seq.strandAt_posOf, toTilde_of_ofTilde hs']
        rw [hX, mul_assoc, ← map_mul]
        exact hp _
  refine LinearMap.pi_ext fun j p => ?_
  have := key j p 1
  rwa [map_one, mul_one] at this

/-- The images of the generators satisfy the KLR relations for `stQ`: both sides act in the same
way in the faithful polynomial representation of the chamber algebra, as they do in the KLR
polynomial representation. -/
theorem stFreeHom_rel (hD : Γ.Dagger) (hE : ∀ e, Γ.head e ≠ Γ.tail e)
    (hl : ∀ c, Γ.loop c = none) (hϖ : StrictMono ϖ) (hw0 : ∀ e, Γ.weight e = 0)
    (hS : Γ.Standing) ⦃x y : FreeAlgebra k (KLR.Gen (stendhalWeight ℓ ν))⦄
    (h : KLR.Rel k (stQ Γ Λ) (stendhalWeight ℓ ν) x y) :
    stFreeHom ν k Λ hϖ hw0 x = stFreeHom ν k Λ hϖ hw0 y := by
  have hΓ := WeightedGraph.crawleyBoeveyIn_psymm (Λ := Λ) (ϖ := ϖ) (psymm_of_loop hl)
  apply chamberRep_injective (WeightedGraph.crawleyBoeveyIn_dagger hD hϖ.injective)
    (WeightedGraph.crawleyBoeveyIn_noZeroLoops fun e he => absurd he (hE e)) hΓ
    (WeightedGraph.crawleyBoeveyIn_isRegular_factor hS)
    (fun Q a b ha => by rw [loop_crawleyBoeveyIn hl] at ha; cases ha)
  have h₀ := GalleryAlgebra.redWeight_zeroStrand (Multiset.toFinsupp ν)
  refine eq_of_comp_stRenOp (chamberOp_commute_mulXOp h₀ hΓ _)
    (chamberOp_commute_mulXOp h₀ hΓ _) ?_
  rw [chamberRep_stFreeHom hD hE hl, chamberRep_stFreeHom hD hE hl,
    KLR.PolyRep.freeRep_rel (fun _ _ _ => rfl) h]

variable (Γ ν k Λ) in
/-- **The map of Theorem 3.5** (Webster, arXiv:1209.2463v4, §3.2): the KLR algebra on the black
and red strands, with the polynomials `stQ`, maps to the weighted KLR algebra of the
Crawley-Boevey graph on the family of Stendhal chambers. A red strand goes to a ghost of the
`0`-strand; a black/red crossing with the black strand on the left is rescaled by
`(-1)^{α_a^∨(λ_r)}`.

The hypotheses `hE` (no edge from a vertex to itself) and `hl` (no loops) say together that `Γ`
has no loops (an edge from a vertex to itself of weight `0` is a loop in Webster's encoding).
This is the setting of Webster's Theorem 3.5: `T̃^λ` is built from the KLR algebra of a loop-free
graph. They are not route hypotheses: with a loop the same-colour KLR relations fail in the
faithful polynomial representation. -/
noncomputable def stKLRHom (hD : Γ.Dagger) (hE : ∀ e, Γ.head e ≠ Γ.tail e)
    (hl : ∀ c, Γ.loop c = none) (hϖ : StrictMono ϖ) (hw0 : ∀ e, Γ.weight e = 0)
    (hS : Γ.Standing) :
    KLR.KLRAlgebra k (stQ Γ Λ) (stendhalWeight ℓ ν) →ₐ[k]
      ChamberAlgebra k (stFull (ν := ν) Λ hϖ hw0) :=
  RingQuot.liftAlgHom k ⟨stFreeHom ν k Λ hϖ hw0, stFreeHom_rel hD hE hl hϖ hw0 hS⟩

theorem chamberRep_stKLRHom (hD : Γ.Dagger) (hE : ∀ e, Γ.head e ≠ Γ.tail e)
    (hl : ∀ c, Γ.loop c = none) (hϖ : StrictMono ϖ) (hw0 : ∀ e, Γ.weight e = 0)
    (hS : Γ.Standing) (x : FreeAlgebra k (KLR.Gen (stendhalWeight ℓ ν))) :
    stKLRHom ν k Γ Λ hD hE hl hϖ hw0 hS (RingQuot.mkAlgHom k _ x) =
      stFreeHom ν k Λ hϖ hw0 x :=
  RingQuot.liftAlgHom_mkAlgHom_apply _ _ _ _

end Hom

end Categorification.Stendhal
