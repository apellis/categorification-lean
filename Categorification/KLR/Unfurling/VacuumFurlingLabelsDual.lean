/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Unfurling.VacuumFurlingLabels
import Categorification.KLR.Unfurling.VacuumLabelLocDual

/-!
# The counterclockwise bubbles of a furled action at one block

B. Webster, *Unfurling Khovanov–Lauda–Rouquier algebras*, arXiv:1603.06311v3, proof of the
theorem with label `nondegenerate`, for a weight `⟨h_i, λ⟩ ≥ 0`. This is the mirror of
`VacuumFurlingLabels`. For the furled action of `g` (`TwoRep.Furling`) on an object `M` of weight
`λ` concentrated at one block `β₀`, it supplies the label data of `ccw_app_eq_lwSeq` at `β₀`:

* the highest weight labels are the relevant edges `e : β₀ - a → β₀` into `β₀`: `E_i F_i M` at
  `β₀` is the sum of the summands `E_a F_a M_{β₀}` (`sum_ιIn_πIn`), on which the dot of `g` is
  `ϖ_a(y)` (`πIn_dot`) and the counit of `g` is the counit of the label (`πIn_counit`); if
  `(ϖ_a(y) - z_a)^{h_a} = 0` on `E_a F_a M_{β₀}`, then `D - z` is invertible on `E_i F_i M` at
  `β₀` for every other scalar `z` (`exists_efDot_inverse`);
* the lowest weight labels are the relevant edges `e : β₀ → β₀ + b` out of `β₀`: the projection
  of `F_i E_i M` onto the summand of `e`, followed by the `♣`-caps of Rouquier's data of the label
  `b` at the weight of `β₀`, form a chain of length `-⟨h_b, wt β₀⟩` (`chainOut`), on which the dot
  of `g` acts by `ϖ_b(y)` (`dot_sub_chainOut`) and the unit of `g` by the unit of the label
  (`unit_chainOut`).

The main result `ccw_app_furled` evaluates the counterclockwise bubbles of Rouquier's data of `g`
at `M_{β₀}`, for a weight `⟨h_i, λ⟩ ≥ 0`.

## Main results

* `sum_ιIn_πIn`, `πIn_dot`, `πIn_counit`, `exists_efDot_inverse`.
* `chainOut`, `unit_chainOut`, `dot_sub_chainOut`.
* `ccw_app_furled`.
-/

noncomputable section

namespace Categorification.KLR.Unfurling

open CategoryTheory CategoryTheory.Bicategory CategoryTheory.Limits TwoRep TwoRep.Furling

universe wk u₁ u₂ u₃ u₄ v₁

/-! ## Generic lemmas -/

section Comp

variable {L : Type*} [CommRing L] {C : Type*} [Category C] [Preadditive C] [Linear L C]

/-- A linear functor commutes with polynomials in an endomorphism. -/
theorem map_aeval {C' : Type*} [Category C'] [Preadditive C'] [Linear L C'] (G : C ⥤ C')
    [G.Additive] [G.Linear L] {Y : C} (D : End Y) (p : Polynomial L) :
    G.map (Polynomial.aeval D p : End Y) =
      (Polynomial.aeval (R := L) (A := End (G.obj Y)) (G.map D) p) := by
  let φ : End Y →ₐ[L] End (G.obj Y) :=
    { toFun := G.map, map_one' := G.map_id Y, map_mul' := fun f g => G.map_comp g f,
      map_zero' := G.map_zero _ _, map_add' := fun f g => G.map_add,
      commutes' := fun r => by
        change G.map (algebraMap L (End Y) r) = algebraMap L (End (G.obj Y)) r
        rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, End.one_def,
          End.one_def, G.map_smul, G.map_id] }
  exact (Polynomial.aeval_algHom_apply φ D p).symm

/-- If `Q` is a sum of summands on which `D` acts by `η_a` with `(η_a - z_a)^{h_a} = 0`, then
`∏ₐ (D - z_a)^{h_a} = 0`. -/
theorem aeval_eq_zero_of_decomp {A : Type*} [Fintype A] {Q : C} {W : A → C}
    (ι : ∀ a, Q ⟶ W a) (π : ∀ a, W a ⟶ Q) (hπι : ∑ a, ι a ≫ π a = 𝟙 Q) (D : End Q)
    (η : ∀ a, End (W a)) (hη : ∀ a, π a ≫ D = η a ≫ π a) (z : A → L) (hp : A → ℕ)
    (hnil : ∀ a, ((η a - algebraMap L _ (z a)) ^ hp a : End (W a)) = 0) :
    (Polynomial.aeval D (∏ a, (Polynomial.X - Polynomial.C (z a)) ^ hp a) : End Q) = 0 := by
  rw [← Category.id_comp (Polynomial.aeval D _ : End Q), ← hπι, Preadditive.sum_comp]
  refine Finset.sum_eq_zero fun a _ => ?_
  rw [Category.assoc, comp_aeval _ _ _ (hη a)]
  obtain ⟨r, hr⟩ := Finset.dvd_prod_of_mem (fun a => (Polynomial.X - Polynomial.C (z a)) ^ hp a)
    (Finset.mem_univ a)
  rw [hr, map_mul, map_pow, map_sub, Polynomial.aeval_X, Polynomial.aeval_C, hnil, zero_mul,
    zero_comp, comp_zero]

/-- A unit followed by a section of a summand and a chain: `(u ≫ G(g)) ≫ G(π) ≫ c = u ≫ c`
when `g ≫ π = 1`. -/
theorem comp_map_comp_eq' {D : Type*} [Category D] {D' : Type*} [Category D'] (G : D ⥤ D')
    {A B : D} {V Z : D'} (u : V ⟶ G.obj A) (g : A ⟶ B) (π : B ⟶ A) (c : G.obj A ⟶ Z)
    (hg : g ≫ π = 𝟙 A) : (u ≫ G.map g) ≫ G.map π ≫ c = u ≫ c := by
  rw [Category.assoc, ← Category.assoc (G.map g), ← G.map_comp, hg, G.map_id, Category.id_comp]

/-- A section of a summand followed by a counit: `(G(j) ≫ g) ≫ κ = κ'` when
`g ≫ κ = G(π) ≫ κ'` and `j ≫ π = 1`. -/
theorem map_comp_comp_eq {D : Type*} [Category D] {D' : Type*} [Category D'] (G : D ⥤ D')
    {A B : D} {Z V : D'} (j : A ⟶ B) (π : B ⟶ A) (g : G.obj B ⟶ Z) (κ : Z ⟶ V)
    (κ' : G.obj A ⟶ V) (hg : g ≫ κ = G.map π ≫ κ') (hj : j ≫ π = 𝟙 A) :
    (G.map j ≫ g) ≫ κ = κ' := by
  rw [Category.assoc, hg, ← Category.assoc, ← G.map_comp, hj, G.map_id, Category.id_comp]

/-- Distributing two morphisms over a linear combination. -/
theorem comp_comp_sum_smul {A B Z V : C} (f : A ⟶ B) (g : B ⟶ Z) (c : ℕ → (Z ⟶ V))
    (a : ℕ → L) (s : Finset ℕ) :
    f ≫ g ≫ ∑ j ∈ s, a j • c j = ∑ j ∈ s, a j • (f ≫ g ≫ c j) := by
  rw [Preadditive.comp_sum, Preadditive.comp_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Linear.comp_smul, Linear.comp_smul]

/-- Moving a shifted dot through a projection onto a summand. -/
theorem sub_comp_comp {Q P R V : C} (π : Q ⟶ P) (j : P ⟶ R) (c : R ⟶ V) (Dq : End Q)
    (ηB : End P) (ηA : End R) (hπ : π ≫ ηB = Dq ≫ π) (hj : j ≫ ηA = ηB ≫ j) (a : L) :
    (Dq - algebraMap L (End Q) a : End Q) ≫ π ≫ j ≫ c =
      π ≫ j ≫ (ηA - algebraMap L (End R) a : End R) ≫ c := by
  rw [← Category.assoc, ← comp_sub_algebraMap π Dq ηB hπ a, Category.assoc,
    ← Category.assoc j, comp_sub_algebraMap j ηB ηA hj a, Category.assoc]

end Comp

variable {k : Type wk} [Field k]
  {J : Type u₁} {I : Type*} {Cc : QuantumGroup.CartanDatum J} {C : QuantumGroup.CartanDatum I}
  {Xc Yc : Type u₃} [AddCommGroup Xc] [AddCommGroup Yc] {X Y : Type u₄} [AddCommGroup X]
  [AddCommGroup Y] {RDc : QuantumGroup.UDot.WeightDatum Cc Xc Yc}
  {RD : QuantumGroup.UDot.WeightDatum C X Y} (Φ : Furling RDc RD)
  (S : RouqFamily (B := LinearCat.{wk, v₁, u₂} k) RDc)
  [∀ x, HasFiniteBiproducts (S.obj x : Type u₂)]

/-! ## The summands of `E_i N` -/

section Proj

variable (ϖ : J → Polynomial k) (i : I) {l₀ l : X} (h₀ : l₀ + RD.iX i = l)

/-- The projection of `E_i N` onto the summand of an edge. -/
abbrev projE (N : ∀ β : Φ.Blk l₀, Φ.blkCat S β.1) {γ : Φ.Blk l}
    (p : {e : Φ.Edge i l₀ // e.tgt h₀ = γ}) :
    (Φ.E S i h₀).obj.obj N γ ⟶ (Φ.Ea S h₀ p.1 γ p.2).obj (N p.1.src) :=
  biproduct.π (fun q : {e : Φ.Edge i l₀ // e.tgt h₀ = γ} =>
    (Φ.Ea S h₀ q.1 γ q.2).obj ((blockRes Edge.src (Φ.resSrc S)).obj N q.1)) p

theorem genE_projE (N : ∀ β : Φ.Blk l₀, Φ.blkCat S β.1) {γ : Φ.Blk l}
    (p : {e : Φ.Edge i l₀ // e.tgt h₀ = γ}) :
    genE Φ S i h₀ N p ≫ projE Φ S i h₀ N p = 𝟙 _ :=
  biproduct.ι_π_self _ _

theorem sum_projE_genE (N : ∀ β : Φ.Blk l₀, Φ.blkCat S β.1) (γ : Φ.Blk l) :
    ∑ p : {e : Φ.Edge i l₀ // e.tgt h₀ = γ}, projE Φ S i h₀ N p ≫ genE Φ S i h₀ N p =
      𝟙 ((Φ.E S i h₀).obj.obj N γ) :=
  IsBilimit.total (biproduct.isBilimit _)

/-- The dot of `g` on the summand of label `a`, on the projection side. -/
theorem dot_projE (N : ∀ β : Φ.Blk l₀, Φ.blkCat S β.1) {γ : Φ.Blk l}
    (p : {e : Φ.Edge i l₀ // e.tgt h₀ = γ}) :
    (dot Φ S ϖ i h₀).hom.app N γ ≫ projE Φ S i h₀ N p =
      projE Φ S i h₀ N p ≫ (Polynomial.aeval
        (show End (S.E p.1.lbl (wt_tgt h₀ p.1 p.2)) from S.dot p.1.lbl (wt_tgt h₀ p.1 p.2))
        (ϖ p.1.lbl)).hom.app (N p.1.src) :=
  biproduct.map_π (fun q : {e : Φ.Edge i l₀ // e.tgt h₀ = γ} =>
    (dotA Φ S ϖ h₀ q.1 γ q.2).app ((blockRes Edge.src (Φ.resSrc S)).obj N q.1)) p

/-- Two edges with the same source and target coincide. -/
theorem Edge.eq_of_src_tgt {e e' : Φ.Edge i l₀} (hs : e'.src = e.src)
    (ht : e'.tgt h₀ = e.tgt h₀) : e' = e := by
  refine Edge.ext hs ?_
  have h1 := congrArg Subtype.val ht
  simp only [Edge.tgt_val, hs] at h1
  exact Finsupp.single_left_injective one_ne_zero (add_left_cancel h1)

/-- For `N` concentrated at the target of `e`, the summand of `e` is all of `F_i N` at the source
of `e`. -/
theorem projF_injF (N : ∀ β : Φ.Blk l, Φ.blkCat S β.1) (e : Φ.Edge i l₀)
    (hN : ∀ β, β ≠ e.tgt h₀ → IsZero (N β)) :
    projF Φ S i h₀ N e ≫ injF Φ S i h₀ N e = 𝟙 _ := by
  refine Eq.trans ?_ (IsBilimit.total (biproduct.isBilimit
    (fun p : {e' : Φ.Edge i l₀ // e'.src = e.src} =>
      (Φ.incSrc S p.1 e.src p.2).obj ((blockRes (Edge.tgt h₀) (Φ.Fa S h₀)).obj N p.1))))
  rw [Finset.sum_eq_single ⟨e, rfl⟩]
  · rfl
  · intro q _ hq
    have hne : q.1.tgt h₀ ≠ e.tgt h₀ := fun ht =>
      hq (Subtype.ext (Edge.eq_of_src_tgt Φ i h₀ q.2 ht))
    have hZ : IsZero ((Φ.incSrc S q.1 e.src q.2).obj
        ((Φ.Fa S h₀ q.1 (q.1.tgt h₀) rfl).obj (N (q.1.tgt h₀)))) :=
      Functor.map_isZero _ (Functor.map_isZero _ (hN _ hne))
    try dsimp only
    exact (congrArg (· ≫ _) (hZ.eq_of_tgt _ 0)).trans zero_comp
  · intro h; exact absurd (Finset.mem_univ _) h

end Proj

/-! ## The highest weight labels: edges into the block -/

section In

variable (ϖ : J → Polynomial k) (i : I) {l₀ l : X} (h₀ : l₀ + RD.iX i = l)
  (M : ∀ β : Φ.Blk l, Φ.blkCat S β.1) (β₀ : Φ.Blk l)

/-- The summand `E_a F_a M_{β₀}` of `E_i F_i M` at `β₀`, for an edge into `β₀`. -/
abbrev WIn (p : InEdge Φ i h₀ β₀) : Φ.blkCat S β₀.1 :=
  (Φ.Ea S h₀ p.1 β₀ p.2).obj ((Φ.Fa S h₀ p.1 β₀ p.2).obj (M β₀))

/-- The inclusion of the summand of an edge into `E_i F_i M` at `β₀`. -/
def πIn (p : InEdge Φ i h₀ β₀) : WIn Φ S i h₀ M β₀ p ⟶
    (Φ.E S i h₀).obj.obj ((Φ.F S i h₀).obj.obj M) β₀ := by
  obtain ⟨e, he⟩ := p
  subst he
  exact (Φ.Ea S h₀ e (e.tgt h₀) rfl).map (injF Φ S i h₀ M e) ≫
    genE Φ S i h₀ ((Φ.F S i h₀).obj.obj M) ⟨e, rfl⟩

/-- The projection of `E_i F_i M` at `β₀` onto the summand of an edge. -/
def ιIn (p : InEdge Φ i h₀ β₀) : (Φ.E S i h₀).obj.obj ((Φ.F S i h₀).obj.obj M) β₀ ⟶
    WIn Φ S i h₀ M β₀ p := by
  obtain ⟨e, he⟩ := p
  subst he
  exact projE Φ S i h₀ ((Φ.F S i h₀).obj.obj M) ⟨e, rfl⟩ ≫
    (Φ.Ea S h₀ e (e.tgt h₀) rfl).map (projF Φ S i h₀ M e)

/-- The dot `ϖ_a(y)` on `E_a F_a M_{β₀}`. -/
abbrev labelDotIn (p : InEdge Φ i h₀ β₀) : End (WIn Φ S i h₀ M β₀ p) :=
  (Polynomial.aeval (show End (S.E p.1.lbl (wt_tgt h₀ p.1 p.2)) from
    S.dot p.1.lbl (wt_tgt h₀ p.1 p.2)) (ϖ p.1.lbl)).hom.app
      ((Φ.Fa S h₀ p.1 β₀ p.2).obj (M β₀))

theorem ιIn_πIn (hM : ∀ β, β ≠ β₀ → IsZero (M β)) (p : InEdge Φ i h₀ β₀) :
    ιIn Φ S i h₀ M β₀ p ≫ πIn Φ S i h₀ M β₀ p =
      projE Φ S i h₀ ((Φ.F S i h₀).obj.obj M) p ≫ genE Φ S i h₀ ((Φ.F S i h₀).obj.obj M) p := by
  obtain ⟨e, rfl⟩ := p
  change (projE Φ S i h₀ ((Φ.F S i h₀).obj.obj M) ⟨e, rfl⟩ ≫
    (Φ.Ea S h₀ e (e.tgt h₀) rfl).map (projF Φ S i h₀ M e)) ≫
      (Φ.Ea S h₀ e (e.tgt h₀) rfl).map (injF Φ S i h₀ M e) ≫
        genE Φ S i h₀ ((Φ.F S i h₀).obj.obj M) ⟨e, rfl⟩ = _
  rw [Category.assoc, ← Category.assoc ((Φ.Ea S h₀ e (e.tgt h₀) rfl).map _),
    ← CategoryTheory.Functor.map_comp, projF_injF Φ S i h₀ M e hM,
    CategoryTheory.Functor.map_id, Category.id_comp]

/-- **`E_i F_i M` at `β₀` is the sum of the summands of the edges into `β₀`**, for `M`
concentrated at `β₀`. -/
theorem sum_ιIn_πIn (hM : ∀ β, β ≠ β₀ → IsZero (M β)) :
    ∑ p, ιIn Φ S i h₀ M β₀ p ≫ πIn Φ S i h₀ M β₀ p =
      𝟙 ((Φ.E S i h₀).obj.obj ((Φ.F S i h₀).obj.obj M) β₀) := by
  rw [Finset.sum_congr rfl fun p _ => ιIn_πIn Φ S i h₀ M β₀ hM p]
  exact sum_projE_genE Φ S i h₀ _ β₀

/-- The dot of `g` on the summand of an edge into `β₀` is `ϖ_a(y)`. -/
theorem πIn_dot (p : InEdge Φ i h₀ β₀) :
    πIn Φ S i h₀ M β₀ p ≫ (dot Φ S ϖ i h₀).hom.app ((Φ.F S i h₀).obj.obj M) β₀ =
      labelDotIn Φ S ϖ i h₀ M β₀ p ≫ πIn Φ S i h₀ M β₀ p := by
  obtain ⟨e, rfl⟩ := p
  let η := (Polynomial.aeval
    (show End (S.E e.lbl (wt_tgt h₀ e rfl)) from S.dot e.lbl (wt_tgt h₀ e rfl)) (ϖ e.lbl)).hom
  have hnat : (Φ.Ea S h₀ e (e.tgt h₀) rfl).map (injF Φ S i h₀ M e) ≫
      η.app ((Φ.F S i h₀).obj.obj M e.src) =
        η.app ((Φ.Fa S h₀ e (e.tgt h₀) rfl).obj (M (e.tgt h₀))) ≫
          (Φ.Ea S h₀ e (e.tgt h₀) rfl).map (injF Φ S i h₀ M e) := η.naturality _
  change ((Φ.Ea S h₀ e (e.tgt h₀) rfl).map (injF Φ S i h₀ M e) ≫
    genE Φ S i h₀ ((Φ.F S i h₀).obj.obj M) ⟨e, rfl⟩) ≫ _ =
      η.app ((Φ.Fa S h₀ e (e.tgt h₀) rfl).obj (M (e.tgt h₀))) ≫
        (Φ.Ea S h₀ e (e.tgt h₀) rfl).map (injF Φ S i h₀ M e) ≫
          genE Φ S i h₀ ((Φ.F S i h₀).obj.obj M) ⟨e, rfl⟩
  rw [Category.assoc, genE_dot, ← Category.assoc, hnat, Category.assoc]

/-- The counit of `g` on the summand of an edge into `β₀` is the counit of the label. -/
theorem πIn_counit (p : InEdge Φ i h₀ β₀) :
    πIn Φ S i h₀ M β₀ p ≫ (Φ.adj S i h₀).counit.hom.app M β₀ =
      (Φ.adjA S h₀ p.1 β₀ p.2).counit.app (M β₀) := by
  obtain ⟨e, rfl⟩ := p
  change ((Φ.Ea S h₀ e (e.tgt h₀) rfl).map (injF Φ S i h₀ M e) ≫
    genE Φ S i h₀ ((Φ.F S i h₀).obj.obj M) ⟨e, rfl⟩) ≫
      (Φ.adj S i h₀).counit.hom.app M (e.tgt h₀) = _
  exact map_comp_comp_eq (Φ.Ea S h₀ e (e.tgt h₀) rfl) (injF Φ S i h₀ M e)
    (projF Φ S i h₀ M e) (genE Φ S i h₀ ((Φ.F S i h₀).obj.obj M) ⟨e, rfl⟩)
    ((Φ.adj S i h₀).counit.hom.app M (e.tgt h₀))
    ((Φ.adjA S h₀ e (e.tgt h₀) rfl).counit.app (M (e.tgt h₀)))
    (genE_counit Φ S i h₀ M e) (injF_projF Φ S i h₀ M e)

/-- **`D - z` is invertible on `E_i F_i M` at `β₀`** for a scalar `z` different from the `z_a`
with `h_a ≠ 0`, if `(ϖ_a(y) - z_a)^{h_a} = 0` on `E_a F_a M_{β₀}`. -/
theorem exists_efDot_inverse (hM : ∀ β, β ≠ β₀ → IsZero (M β)) (z : InEdge Φ i h₀ β₀ → k)
    (hp : InEdge Φ i h₀ β₀ → ℕ)
    (hnil : ∀ p, ((labelDotIn Φ S ϖ i h₀ M β₀ p - algebraMap k _ (z p)) ^ hp p :
      End (WIn Φ S i h₀ M β₀ p)) = 0)
    (zb : k) (hzb : ∀ p, hp p ≠ 0 → z p ≠ zb) :
    ∃ w : End ((Φ.E S i h₀).obj.obj ((Φ.F S i h₀).obj.obj M) β₀),
      ((show End ((Φ.E S i h₀).obj.obj ((Φ.F S i h₀).obj.obj M) β₀) from
        (dot Φ S ϖ i h₀).hom.app ((Φ.F S i h₀).obj.obj M) β₀) - algebraMap k _ zb) * w = 1 ∧
      w * ((show End ((Φ.E S i h₀).obj.obj ((Φ.F S i h₀).obj.obj M) β₀) from
        (dot Φ S ϖ i h₀).hom.app ((Φ.F S i h₀).obj.obj M) β₀) - algebraMap k _ zb) = 1 :=
  exists_inverse_sub_algebraMap _ _ (aeval_eq_zero_of_decomp (ιIn Φ S i h₀ M β₀)
    (πIn Φ S i h₀ M β₀) (sum_ιIn_πIn Φ S i h₀ M β₀ hM) _ (labelDotIn Φ S ϖ i h₀ M β₀)
    (πIn_dot Φ S ϖ i h₀ M β₀) z hp hnil) zb (by
    rw [isUnit_iff_ne_zero, Polynomial.eval_prod, Finset.prod_ne_zero_iff]
    intro p _
    rw [Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    by_cases h0 : hp p = 0
    · rw [h0, pow_zero]; exact one_ne_zero
    · exact pow_ne_zero _ (sub_ne_zero.mpr (hzb p h0).symm))

end In

/-! ## The lowest weight labels: edges out of the block -/

section Out

variable (ϖ : J → Polynomial k) (i : I) {l l' : X} (h : l + RD.iX i = l')
  (M : ∀ β : Φ.Blk l, Φ.blkCat S β.1) (β₀ : Φ.Blk l)

/-- The edges out of `β₀` whose label has negative weight at `β₀`. -/
abbrev NegOutEdge :=
  {p : OutEdge Φ i β₀ // RDc.pair (RDc.iY p.1.lbl) (Φ.wtT β₀.1) < 0}

instance : Fintype (NegOutEdge Φ i β₀) := Fintype.ofFinite _

/-- Rouquier's data of the label of an edge out of a block, at the weight of that block. -/
abbrev labelLocOut (e : Φ.Edge i l) :=
  S.loc e.lbl (sub_add_cancel (Φ.wtT e.src.1) (RDc.iX e.lbl)) (wt_tgt h e rfl)

/-- The `m`-th `♣`-cap of the label of an edge `e` out of a block, on `F_i E_i M`. -/
def cOut (e : Φ.Edge i l) (m : ℕ) : feAt Φ S i h M e.src ⟶ M e.src :=
  biproduct.π (feSummand Φ S i h M e.src) ⟨e, rfl⟩ ≫
    (Φ.Fa S h e (e.tgt h) rfl).map (projE Φ S i h M ⟨e, rfl⟩) ≫
      ((labelLocOut Φ S i h e).capN m).hom.app (M e.src)

/-- **The chains of a lowest weight label**: the `m`-th `♣`-cap of the label of an edge out of
`β₀`, on `F_i E_i M` at `β₀`. -/
def chainOut (p : OutEdge Φ i β₀) (m : ℕ) : feAt Φ S i h M β₀ ⟶ M β₀ := by
  obtain ⟨e, he⟩ := p
  subst he
  exact cOut Φ S i h M e m

omit [∀ x, HasFiniteBiproducts (S.obj x : Type u₂)] in
/-- A common nilpotency order of the two dots of the label of an edge out of a block. -/
theorem exists_labelLocOut_nilpotent
    (hnil : ∀ (c : J) {x y : Xc} (hc : x + RDc.iX c = y), ∃ n, powComp (S.dot c hc) n = 0)
    (e : Φ.Edge i l) :
    ∃ n, powComp (S.dot e.lbl (sub_add_cancel (Φ.wtT e.src.1) (RDc.iX e.lbl))) n = 0 ∧
      powComp (S.dot e.lbl (wt_tgt h e rfl)) n = 0 := by
  obtain ⟨n₁, h₁⟩ := hnil e.lbl (sub_add_cancel (Φ.wtT e.src.1) (RDc.iX e.lbl))
  obtain ⟨n₂, h₂⟩ := hnil e.lbl (wt_tgt h e rfl)
  exact ⟨n₁ + n₂, powComp_eq_zero_of_le _ h₁ (Nat.le_add_right _ _),
    powComp_eq_zero_of_le _ h₂ (Nat.le_add_left _ _)⟩

/-- **The unit of `g` on the chains**: `κ ≫ c_{b,m} = δ_{m,0}` (Brundan (3.7) for the label). -/
theorem unit_chainOut
    (hnil : ∀ (c : J) {x y : Xc} (hc : x + RDc.iX c = y), ∃ n, powComp (S.dot c hc) n = 0)
    [IsReduced (End (M β₀))] (p : OutEdge Φ i β₀) (m : ℕ)
    (hm : m < (-RDc.pair (RDc.iY p.1.lbl) (Φ.wtT β₀.1)).toNat) :
    feUnit Φ S i h M β₀ ≫ chainOut Φ S i h M β₀ p m = if m = 0 then 𝟙 _ else 0 := by
  obtain ⟨e, rfl⟩ := p
  obtain ⟨n, hx₁, hx₂⟩ := exists_labelLocOut_nilpotent Φ S i h hnil e
  have key := cupD_app_capN_app (labelLocOut Φ S i h e) (M e.src) hx₁ hx₂ hm 0
  rw [pow_zero, End.one_def] at key
  have h2 : feUnit Φ S i h M e.src ≫ biproduct.π (feSummand Φ S i h M e.src) ⟨e, rfl⟩ =
      (Φ.adjA S h e (e.tgt h) rfl).unit.app (M e.src) ≫
        (Φ.Fa S h e (e.tgt h) rfl).map (genE Φ S i h M ⟨e, rfl⟩) :=
    unit_projF Φ S i h M e
  change feUnit Φ S i h M e.src ≫ cOut Φ S i h M e m = _
  rw [cOut, ← Category.assoc, h2]
  refine (comp_map_comp_eq' (Φ.Fa S h e (e.tgt h) rfl) _ _ _ _
    (genE_projE Φ S i h M ⟨e, rfl⟩)).trans ?_
  refine (congrArg (_ ≫ ·) (Category.id_comp _)).symm.trans (key.trans ?_)
  by_cases hm0 : m = 0
  · subst hm0; rfl
  · simp only [hm0, Ne.symm hm0, ↓reduceIte]
    rfl

/-- **The dot of `g` on the chains**: `(D - ϖ_b(0)) ≫ c_{b,m} = ∑_{j<m} [ϖ_b]_{m-j} c_{b,j}`. -/
theorem dot_sub_chainOut
    (hnil : ∀ (c : J) {x y : Xc} (hc : x + RDc.iX c = y), ∃ n, powComp (S.dot c hc) n = 0)
    [IsReduced (End (M β₀))] (p : OutEdge Φ i β₀)
    (hh : RDc.pair (RDc.iY p.1.lbl) (Φ.wtT β₀.1) ≤ 0)
    (hY : IsZero ((S.E p.1.lbl (sub_add_cancel (Φ.wtT β₀.1) (RDc.iX p.1.lbl))).obj.obj
      ((S.F p.1.lbl (sub_add_cancel (Φ.wtT β₀.1) (RDc.iX p.1.lbl))).obj.obj (M β₀))))
    (m : ℕ) (hm : m < (-RDc.pair (RDc.iY p.1.lbl) (Φ.wtT β₀.1)).toNat) :
    (feDot Φ S ϖ i h M β₀ - algebraMap k _ ((ϖ p.1.lbl).coeff 0) : End _) ≫
        chainOut Φ S i h M β₀ p m =
      ∑ j ∈ Finset.range m, (ϖ p.1.lbl).coeff (m - j) • chainOut Φ S i h M β₀ p j := by
  obtain ⟨e, rfl⟩ := p
  obtain ⟨n, hx₁, hx₂⟩ := exists_labelLocOut_nilpotent Φ S i h hnil e
  have key := aeval_sub_capN_app (labelLocOut Φ S i h e) (M e.src) hh hY hx₁ hx₂ (ϖ e.lbl) hm
  let η := (Polynomial.aeval
    (show End (S.E e.lbl (wt_tgt h e rfl)) from S.dot e.lbl (wt_tgt h e rfl)) (ϖ e.lbl)).hom
  have hη : (show End ((Φ.Fa S h e (e.tgt h) rfl).obj ((Φ.Ea S h e (e.tgt h) rfl).obj
      (M e.src))) from (Φ.Fa S h e (e.tgt h) rfl).map (η.app (M e.src))) =
        Polynomial.aeval (dotAt₂ (x₂ := S.dot e.lbl (wt_tgt h e rfl))
          (R₂ := S.F e.lbl (wt_tgt h e rfl)) (M e.src)) (ϖ e.lbl) :=
    (congrArg (Φ.Fa S h e (e.tgt h) rfl).map (aeval_hom_app _ _ _)).trans
      (map_aeval (Φ.Fa S h e (e.tgt h) rfl) _ _)
  change (feDot Φ S ϖ i h M e.src - _ : End _) ≫ cOut Φ S i h M e m =
    ∑ j ∈ Finset.range m, _ • cOut Φ S i h M e j
  have hj : (Φ.Fa S h e (e.tgt h) rfl).map (projE Φ S i h M ⟨e, rfl⟩) ≫
      (Φ.Fa S h e (e.tgt h) rfl).map (η.app (M e.src)) =
        (Φ.Fa S h e (e.tgt h) rfl).map ((dot Φ S ϖ i h).hom.app M (e.tgt h)) ≫
          (Φ.Fa S h e (e.tgt h) rfl).map (projE Φ S i h M ⟨e, rfl⟩) := by
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
      dot_projE Φ S ϖ i h M ⟨e, rfl⟩]
  refine (sub_comp_comp (biproduct.π (feSummand Φ S i h M e.src) ⟨e, rfl⟩)
    ((Φ.Fa S h e (e.tgt h) rfl).map (projE Φ S i h M ⟨e, rfl⟩))
    (((labelLocOut Φ S i h e).capN m).hom.app (M e.src)) _
    ((Φ.Fa S h e (e.tgt h) rfl).map ((dot Φ S ϖ i h).hom.app M (e.tgt h)))
    ((Φ.Fa S h e (e.tgt h) rfl).map (η.app (M e.src)))
    (feDot_π Φ S ϖ i h M e.src ⟨e, rfl⟩).symm hj _).trans ?_
  refine (congrArg (fun t => biproduct.π (feSummand Φ S i h M e.src) ⟨e, rfl⟩ ≫
    (Φ.Fa S h e (e.tgt h) rfl).map (projE Φ S i h M ⟨e, rfl⟩) ≫ t)
      ((congrArg (fun u => (u - algebraMap k _ ((ϖ e.lbl).coeff 0) : End _) ≫
        ((labelLocOut Φ S i h e).capN m).hom.app (M e.src)) hη).trans key)).trans ?_
  exact comp_comp_sum_smul _ _ _ _ _

end Out

/-! ## The counterclockwise bubbles of a furled action at one block -/

section Bubbles

variable (ϖ : J → Polynomial k) (i : I) {l₀ l l' : X} (h₀ : l₀ + RD.iX i = l)
  (h : l + RD.iX i = l') (M : ∀ β : Φ.Blk l, Φ.blkCat S β.1) (β₀ : Φ.Blk l)

/-- **The counterclockwise bubbles of a furled action at one block** (Webster,
arXiv:1603.06311v3, proof of the theorem with label `nondegenerate`). Let `L` be Rouquier's data
of the colour `i` for the furled action of `g` at a weight `λ` with `⟨h_i, λ⟩ ≥ 0`, and let `M` be
concentrated at the block `β₀`, with `End M_{β₀}` reduced and the dots of `S̃` nilpotent. Suppose

* for the relevant edges `a` into `β₀`: `(ϖ_a(y) - z_a)^{h_a} = 0` on `E_a F_a M_{β₀}`;
* for the relevant edges `b` out of `β₀` whose label has negative weight `⟨h_b, wt β₀⟩` at
  `β₀`: `E_b F_b M_{β₀} = 0`, the constant terms `ϖ_b(0)` are distinct and differ from the `z_a`
  with `h_a ≠ 0`, and the linear coefficients `[ϖ_b]_1` are nonzero;
* `∑ₐ h_a = ⟨h_i, λ⟩ + ∑_b Λ_b > 0`, where `Λ_b = max(-⟨h_b, wt β₀⟩, 0)` over all edges out of
  `β₀`.

Then the counterclockwise bubble with `m` dots acts on `M_{β₀}` by
`[t^{m+1-⟨h_i,λ⟩}] ∏_b (1 - ϖ_b(0) t)^{Λ_b} ∏ₐ (1 - z_a t)^{-h_a}`. Edges out of `β₀` whose label
has weight `≥ 0` contribute the factor `1`. -/
theorem ccw_app_furled {τ : Φ.E S i h₀ ≫ Φ.E S i h ⟶ Φ.E S i h₀ ≫ Φ.E S i h} {hl : ℤ}
    (L : RouqLoc (Φ.adj S i h₀) (Φ.adj S i h) (dot Φ S ϖ i h₀) (dot Φ S ϖ i h) τ hl)
    (hhl : 0 ≤ hl) (hM : ∀ β, β ≠ β₀ → IsZero (M β)) [IsReduced (End (M β₀))]
    (hnilS : ∀ (c : J) {x y : Xc} (hc : x + RDc.iX c = y), ∃ n, powComp (S.dot c hc) n = 0)
    (z : InEdge Φ i h₀ β₀ → k) (hp : InEdge Φ i h₀ β₀ → ℕ)
    (hnil : ∀ p m, hp p ≤ m → ((labelDotIn Φ S ϖ i h₀ M β₀ p - algebraMap k _ (z p)) ^ m :
      End (WIn Φ S i h₀ M β₀ p)) = 0)
    (hY : ∀ p : NegOutEdge Φ i β₀,
      IsZero ((S.E p.1.1.lbl (sub_add_cancel (Φ.wtT β₀.1) (RDc.iX p.1.1.lbl))).obj.obj
        ((S.F p.1.1.lbl (sub_add_cancel (Φ.wtT β₀.1) (RDc.iX p.1.1.lbl))).obj.obj (M β₀))))
    (hzb : Function.Injective fun p : NegOutEdge Φ i β₀ => (ϖ p.1.1.lbl).coeff 0)
    (hsep : ∀ a (b : NegOutEdge Φ i β₀), hp a ≠ 0 → z a ≠ (ϖ b.1.1.lbl).coeff 0)
    (hβ : ∀ p : NegOutEdge Φ i β₀, (ϖ p.1.1.lbl).coeff 1 ≠ 0)
    (hN : ∑ a, hp a = hl.toNat +
      ∑ b : OutEdge Φ i β₀, (-RDc.pair (RDc.iY b.1.lbl) (Φ.wtT β₀.1)).toNat)
    (hNpos : 0 < ∑ a, hp a) {R : Type*} [CommRing R] [Algebra k R] (ev : End (M β₀) →ₐ[k] R)
    (m : ℕ) :
    ev ((L.ccw m).hom.app M β₀) = algebraMap k R (lwSeq hl.toNat
      ((∏ b : OutEdge Φ i β₀, (1 - PowerSeries.C ((ϖ b.1.lbl).coeff 0) * PowerSeries.X) ^
          (-RDc.pair (RDc.iY b.1.lbl) (Φ.wtT β₀.1)).toNat) *
        ((∏ a, oneSubUnit (z a) ^ (-(hp a : ℤ)) : (PowerSeries k)ˣ) : PowerSeries k)) m) := by
  classical
  have hw := fun b : NegOutEdge Φ i β₀ => exists_efDot_inverse Φ S ϖ i h₀ M β₀ hM z hp
    (fun p => hnil p (hp p) le_rfl) ((ϖ b.1.1.lbl).coeff 0) (fun a ha => hsep a b ha)
  have h0 : ∀ b : OutEdge Φ i β₀, ¬ RDc.pair (RDc.iY b.1.lbl) (Φ.wtT β₀.1) < 0 →
      (-RDc.pair (RDc.iY b.1.lbl) (Φ.wtT β₀.1)).toNat = 0 := fun _ hb =>
    Int.toNat_eq_zero.mpr (by omega)
  rw [← prod_subtype_of_one _ _ fun b hb => by rw [h0 b hb, pow_zero]]
  refine ccw_app_eq_lwSeq L (blkEval Φ S M β₀) hhl ev (Wa := WIn Φ S i h₀ M β₀)
    (πIn Φ S i h₀ M β₀) (ιIn Φ S i h₀ M β₀)
    (fun p => (Φ.adjA S h₀ p.1 β₀ p.2).counit.app (M β₀))
    (fun p => labelDotIn Φ S ϖ i h₀ M β₀ p - algebraMap k _ (z p)) z hp
    (sum_ιIn_πIn Φ S i h₀ M β₀ hM) ?_ ?_
    (fun b => (ϖ b.1.1.lbl).coeff 0) hzb _ (fun b => (hw b).choose) ?_ ?_
    (fun b => chainOut Φ S i h M β₀ b.1) (fun b m j => (ϖ b.1.1.lbl).coeff (m - j)) ?_ ?_ ?_
    (hN.trans (congrArg _ (sum_subtype_of_zero _ _ h0).symm)) hNpos m
  · intro n p
    rw [add_sub_cancel]
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (· ≫ _) (comp_pow_of_comp (πIn Φ S i h₀ M β₀ p)
      (labelDotIn Φ S ϖ i h₀ M β₀ p)
      (dotP (R₁ := Φ.F S i h₀) (x₁ := dot Φ S ϖ i h₀) (blkEval Φ S M β₀))
      (πIn_dot Φ S ϖ i h₀ M β₀ p) n)).trans ?_
    exact (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (πIn_counit Φ S i h₀ M β₀ p))
  · intro p m hm
    exact (congrArg (· ≫ _) (hnil p m hm)).trans zero_comp
  · intro b; exact (hw b).choose_spec.1
  · intro b; exact (hw b).choose_spec.2
  · intro b m hm
    exact dot_sub_chainOut Φ S ϖ i h M β₀ hnilS b.1 b.2.le (hY b) m hm
  · intro b m _
    rw [Nat.add_sub_cancel_left]
    exact hβ b
  · intro b m hm
    exact unit_chainOut Φ S i h M β₀ hnilS b.1 m hm

end Bubbles

end Categorification.KLR.Unfurling
