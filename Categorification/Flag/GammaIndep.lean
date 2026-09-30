/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Flag.GammaIndepMat
import Categorification.Flag.GammaIndepBub
import Categorification.Flag.GammaIndepData
import Categorification.Flag.GammaIndepAlg
import Categorification.Diagrams.KL3.SpanningPositive

/-!
# Linear independence of `B_{+i,+j,λ}` from a family of `Γ_N`-like functors

Khovanov–Lauda III (arXiv:0807.3250v1), §6.4 (TeX `sln-2008-ArXiv.tex` l. 9598–9790, the lemma
"There is an isomorphism of graded `𝕜`-algebras `ι'_λ : R(ν) ⊗ Π_λ → U*(E_ν 1_λ, E_ν 1_λ)`",
injectivity): "Injectivity of `ι'_λ` is established by showing that for each `M ∈ ℕ` there exists
some large `N` such that degree `M` elements `ι_λ(D) . D_π`, as `D` and `D_π` run over a basis of
`R(ν)`, respectively `Π_λ`, act by linear independent operators under the 2-representation
`Γ^G_N`. … The bimodule maps `f_D ⊗ g_{D_π}` are linearly independent operators since the
bimodule maps `f_D` and `g_{D_π}` are separately independent and act on algebraically
independent generators".

We prove the abstract form (`linearIndependent_vB`): if, for every bound `B`, there is a
`Γ_N`-like linear functor `F` out of `U(sl_{m₀+1})` (`GammaLike`) which

* sends the upward dots and crossings to single upward dots and crossings with units `d_c`,
  `κ_{cd}` (`UpCompat`), for an injective colour map `ιc`,
* sends the generators of `Π_λ` to multiplication by their `Γ_N`-values `bubVal` (times units)
  in the rightmost region, the colours `ιc c` being not the last one,
* and whose target paths have all blocks larger than `B`,

then the elements `vB μ i j p = ϕ_{ν,λ}(ψ_{ρ w} x^u e_i ⊗ m)_{ij}` (`p = ((i, w, u), m)`,
`w • i = j`) of `HOM_U(E_{+i} 1_λ, E_{+j} 1_λ)` are linearly independent.

The proof follows KL III: the polynomial shadow of `F(ψ_{ρ w} x^u e_i)` is the KL I operator
(`sh_basis`), which are linearly independent (KL I, `linearIndependent_opΨw`), hence already on
finitely many monomials (`exists_finset_separating`); the bubbles multiply the rightmost
region by `bubVal`, whose values under the total Chern classes `chernData` are free variables
(`hLift_bubVal`); the evaluation `evR` into a truncated polynomial ring (degree bound chosen after
the finitely many test monomials) then separates everything.
-/

noncomputable section

namespace Categorification.Flag.Indep

open Categorification.Flag Categorification.KL3.Diagram StringDiagrams CategoryTheory
  Categorification.KLR Categorification.KLR.PolyRep MvPolynomial Categorification.KL3.Diagram.Signed

universe u

variable {K : Type u} [Field K] {m₀ M N : ℕ}

/-! ## Bubble monomials -/

section Bubbles

variable {F : (pres (slRootDatum m₀) K).Presented ⥤ ModuleCat.{u} K}
  {ιF : Obj (psig (slRootDatum m₀)) ⥤ Obj (psig (slRootDatum M))}
  {dnScal : Fin M → Fin M → K} {χ : (psig (slRootDatum M)).Gen → Kˣ}
  (hF : GammaLike F ιF N dnScal χ) {ν : Multiset (Fin m₀)} (μ : Wt m₀) (μ' : Wt M)
  (hv : ∀ s : Seq ν, WOK N (ιF.obj (ob (slRootDatum m₀) μ (ups (KLR.Diagram.word s)))).start
    (ιF.obj (ob (slRootDatum m₀) μ (ups (KLR.Diagram.word s)))).word)
  (he : ∀ s : Seq ν, lastR (ιF.obj (ob (slRootDatum m₀) μ (ups (KLR.Diagram.word s)))).start
    (ιF.obj (ob (slRootDatum m₀) μ (ups (KLR.Diagram.word s)))).word = μ')

/-- The value in the rightmost region of a bubble monomial. -/
def bval (ιc : Fin m₀ → Fin M) (ω : Fin m₀ × ℕ → K) (d : Comp M) (m : (Fin m₀ × ℕ) →₀ ℕ) : H K d :=
  m.prod fun p e => (algebraMap K (H K d) (ω p) * bubVal d (ιc p.1) p.2) ^ e

variable {hF μ μ' hv he}

/-- **Bubble monomials multiply the rightmost region by `bval`.** -/
theorem map_bubAt_monomial [F.Additive] (ιc : Fin m₀ → Fin M) (ω : Fin m₀ × ℕ → K)
    (hbub : ∀ (s : Seq ν) (p : Fin m₀ × ℕ) q z,
      (F.map (bubAt (slRootDatum m₀) K μ (ups (KLR.Diagram.word s))
        (bubGen (slRootDatum m₀) K μ p.1 (p.2 + 1)))).hom (pv hF μ μ' hv he s q z) =
        pv hF μ μ' hv he s q ((algebraMap K _ (ω p) * bubVal (compOf N μ') (ιc p.1) p.2) * z))
    (m : (Fin m₀ × ℕ) →₀ ℕ) (s : Seq ν) (q : MvPolynomial (Fin (Multiset.card ν)) K)
    (z : H K (compOf N μ')) :
    (F.map (bubAt (slRootDatum m₀) K μ (ups (KLR.Diagram.word s))
      (bubMap (slRootDatum m₀) K μ (monomial m 1)).val)).hom (pv hF μ μ' hv he s q z) =
      pv hF μ μ' hv he s q (bval ιc ω (compOf N μ') m * z) := by
  induction m using Finsupp.induction generalizing z with
  | zero =>
    rw [monomial_zero', C_1, map_one, EndOne.val_one, bubAt_id, F.map_id, bval,
      Finsupp.prod_zero_index, one_mul]
    rfl
  | single_add p e m hp he' ih =>
    have hX : bubMap (slRootDatum m₀) K μ (X p) =
        EndOne.of (bubGen (slRootDatum m₀) K μ p.1 (p.2 + 1)) := aeval_X _ _
    rw [monomial_single_add, map_mul, EndOne.val_mul, bubAt_comp, F.map_comp, ModuleCat.hom_comp,
      LinearMap.comp_apply, ih, map_pow, hX]
    have hpow : ∀ (k : ℕ) (z' : H K (compOf N μ')),
        (F.map (bubAt (slRootDatum m₀) K μ (ups (KLR.Diagram.word s))
          (EndOne.of (bubGen (slRootDatum m₀) K μ p.1 (p.2 + 1)) ^ k).val)).hom
          (pv hF μ μ' hv he s q z') =
        pv hF μ μ' hv he s q ((algebraMap K _ (ω p) * bubVal (compOf N μ') (ιc p.1) p.2) ^ k * z') := by
      intro k
      induction k with
      | zero => intro z'; rw [pow_zero, EndOne.val_one, bubAt_id, F.map_id, pow_zero, one_mul]; rfl
      | succ k ihk =>
        intro z'
        rw [pow_succ, EndOne.val_mul, bubAt_comp, F.map_comp, ModuleCat.hom_comp,
          LinearMap.comp_apply]
        rw [show (EndOne.of (bubGen (slRootDatum m₀) K μ p.1 (p.2 + 1))).val =
          bubGen (slRootDatum m₀) K μ p.1 (p.2 + 1) from rfl]
        rw [hbub, ihk, pow_succ]
        congr 1; ring
    rw [hpow, bval, bval, Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]
    rw [Finsupp.prod_single_index (h := fun x e => ((algebraMap K (H K (compOf N μ'))) (ω x) *
      bubVal (compOf N μ') (ιc x.1) x.2) ^ e) (pow_zero _)]
    congr 1; ring

end Bubbles

/-! ## Evaluation -/

section Eval

variable (N) in
/-- All strands of the path are upward and all blocks of all regions are larger than `B`. -/
def RegionsBig (B : ℕ) : Wt M → List (WCol M) → Prop
  | s, [] => ∀ j, B < compOf N s j
  | s, col :: ws => col.l.1 = true ∧ (∀ j, B < compOf N s j) ∧ RegionsBig B col.r ws

variable {D : ℕ}

theorem regionsBig_last {B : ℕ} : ∀ (s : Wt M) (ws : List (WCol M)), RegionsBig N B s ws →
    ∀ j, B < compOf N (lastR s ws) j
  | _, [], h => h
  | _, col :: ws, h => regionsBig_last col.r ws h.2.2

/-- The Chern roots `Ξ_k, …, Ξ_{k+r-1}` of a path of `r` strands. -/
def xiList (k r : ℕ) : List (TrS K M D) := (List.range' k r).map (Xi K M D)

theorem pathHyp_of_regionsBig {B : ℕ} (hDB : D ≤ B) {c : Fin (M + 1) → TrS K M D}
    (hc : GoodData K (wS M) D c) : ∀ (s : Wt M) (ws : List (WCol M)) (k : ℕ),
    RegionsBig N B s ws → PathHyp N s ws (xiList (K := K) (D := D) k ws.length) c
  | s, [], _, h => ⟨hc, fun j => lt_of_le_of_lt hDB (h j)⟩
  | s, col :: ws, k, h => by
    refine ⟨h.1, goodXi_Xi k, fun j => lt_of_le_of_lt hDB (h.2.1 j), ?_⟩
    have := pathHyp_of_regionsBig hDB hc col.r ws (k + 1) h.2.2
    simpa [xiList, List.range'_succ] using this

theorem getD_xiList (r t : ℕ) (ht : t < r) :
    (xiList (K := K) (M := M) (D := D) 0 r).getD t 0 = Xi K M D t := by
  simp [xiList, ht]

theorem aeval_rename_val {r L : ℕ} (hr : r ≤ L) (Q : MvPolynomial (Fin r) K) :
    aeval (fun t => (xiList (K := K) (M := M) (D := D) 0 L).getD t 0) (rename Fin.val Q) =
      mkT K (wS M) D (rename Sum.inl (rename Fin.val Q)) := by
  rw [aeval_rename, rename_rename]
  have : (fun t => (xiList (K := K) (M := M) (D := D) 0 L).getD t 0) ∘ Fin.val =
      fun a : Fin r => mkT K (wS M) D (X (Sum.inl (a : ℕ))) := by
    funext a; simp only [Function.comp_apply]; rw [getD_xiList L a (by omega)]; rfl
  rw [this]
  induction Q using MvPolynomial.induction_on with
  | C a => simp [mkT]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p a hp => simp only [map_mul, hp, aeval_X, rename_X, Function.comp_apply]

variable (pos : Fin M → Prop) [DecidablePred pos]

theorem hLift_bval (ιc : Fin m₀ → Fin M) (hlast : ∀ c, (ιc c : ℕ) + 1 < M) (ω : Fin m₀ × ℕ → K)
    (d : Comp M) (hd : ∀ j, D ≤ d j) (hpos : ∀ c, pos c ↔ 0 ≤ nH d c)
    (m : (Fin m₀ × ℕ) →₀ ℕ) :
    hLift d hd (chernData K M D pos) (coeff_sc_chernData pos) (prod_chernData pos)
      (bval ιc ω d m) =
      algebraMap K _ (m.prod fun p e => (ω p * (-1) ^ (p.2 + 1)) ^ e) *
        mkT K (wS M) D (monomial (m.mapDomain fun p => Sum.inr (ιc p.1, p.2)) 1) := by
  induction m using Finsupp.induction with
  | zero => simp [bval, mkT]
  | single_add p e m hp he ih =>
    have hb := hLift_bubVal (K := K) (D := D) pos d hd hpos (ιc p.1) (hlast p.1) p.2
    have e1 : bval ιc ω d (Finsupp.single p e + m) =
        ((algebraMap K (H K d)) (ω p) * bubVal d (ιc p.1) p.2) ^ e * bval ιc ω d m := by
      rw [bval, bval, Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _),
        Finsupp.prod_single_index (h := fun x e => ((algebraMap K (H K d)) (ω x) *
        bubVal d (ιc x.1) x.2) ^ e) (pow_zero _)]
    have e2 : ((Finsupp.single p e + m).prod fun p e => (ω p * (-1) ^ (p.2 + 1)) ^ e) =
        (ω p * (-1) ^ (p.2 + 1)) ^ e * m.prod fun p e => (ω p * (-1) ^ (p.2 + 1)) ^ e := by
      rw [Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _),
        Finsupp.prod_single_index (h := fun x e => (ω x * (-1) ^ (x.2 + 1)) ^ e) (pow_zero _)]
    have e3 : (monomial ((Finsupp.single p e + m).mapDomain fun p => Sum.inr (ιc p.1, p.2)) 1 :
        MvPolynomial (VarS M) K) = X (Sum.inr (ιc p.1, p.2)) ^ e *
          monomial (m.mapDomain fun p => Sum.inr (ιc p.1, p.2)) 1 := by
      rw [Finsupp.mapDomain_add, Finsupp.mapDomain_single, monomial_single_add]
    rw [e1, map_mul, ih, map_pow, map_mul, AlgHom.commutes, hb, e2, e3, map_mul, map_mul, map_pow]
    simp only [map_neg, map_mul, map_pow, map_one]
    ring

end Eval

/-! ## Auxiliary lemmas -/

section Aux

theorem weight_mapDomain_inl (e : ℕ →₀ ℕ) :
    Finsupp.weight (wS M) (e.mapDomain Sum.inl) = e.sum fun _ n => n := by
  rw [Finsupp.weight_apply, Finsupp.sum_mapDomain_index (h := fun i c => c • wS M i)
    (fun _ => zero_smul _ _) (fun _ _ _ => add_smul _ _ _)]
  simp [wS]

theorem weight_support_le (P : MvPolynomial ℕ K) (M' : VarS M →₀ ℕ) (a : K)
    (s : VarS M →₀ ℕ) (hs : s ∈ (rename Sum.inl P * monomial M' a).support) :
    Finsupp.weight (wS M) s ≤ P.totalDegree + Finsupp.weight (wS M) M' := by
  classical
  obtain ⟨e₁, he₁, e₂, he₂, rfl⟩ := Finset.mem_add.1 (support_mul _ _ hs)
  rw [support_rename_of_injective Sum.inl_injective, Finset.mem_image] at he₁
  obtain ⟨e, he, rfl⟩ := he₁
  have h2 : e₂ = M' := by
    by_contra h
    have := support_monomial_subset he₂
    exact h (Finset.mem_singleton.1 this)
  subst h2
  rw [map_add, weight_mapDomain_inl]
  exact Nat.add_le_add_right (le_totalDegree he) _

/-- **Separating the bubble variables**: in `k[ℕ ⊕ τ]`, a vanishing combination of polynomials in
the first variables times distinct monomials in the second variables has vanishing coefficients. -/
theorem sum_eq_zero_of_classes {ι τ : Type*} [DecidableEq τ] (S : Finset ι) (a : ι → K)
    (P : ι → MvPolynomial ℕ K) (mm : ι → τ →₀ ℕ)
    (h : ∑ x ∈ S, rename Sum.inl (P x) * monomial ((mm x).mapDomain Sum.inr) (a x) = 0)
    (m0 : τ →₀ ℕ) : ∑ x ∈ S.filter (fun x => mm x = m0), a x • P x = 0 := by
  ext e
  have := congrArg (fun p : MvPolynomial (ℕ ⊕ τ) K => p.coeff (Finsupp.sumElim e m0)) h
  rw [coeff_sum, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at this
  rw [coeff_sum, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply, ← this, Finset.sum_filter]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [show (monomial ((mm x).mapDomain Sum.inr) (a x) : MvPolynomial (ℕ ⊕ τ) K) =
      C (a x) * monomial ((mm x).mapDomain Sum.inr) 1 by rw [C_mul_monomial, mul_one],
    ← mul_assoc, mul_comm (rename Sum.inl (P x)) (C (a x)), mul_assoc, coeff_C_mul,
    coeff_rename_inl_mul_monomial_inr, coeff_smul, smul_eq_mul]
  split_ifs <;> simp

end Aux

section Aux2

variable {ν : Multiset (Fin m₀)}

/-- The operator of KL I of the basis element `ψ_{ρ w} x^u e_i`, on `Pol_i`, as a map to
`Pol_{w • i}`. -/
theorem op_single_apply (P : Fin m₀ → Fin m₀ → MvPolynomial (Fin 2) K)
    (ρ : Equiv.Perm (Fin (Multiset.card ν)) → List ℕ)
    (hρ : ∀ w, TypeA.wordProd (Multiset.card ν) (ρ w) = w) (i : Seq ν)
    (w : Equiv.Perm (Fin (Multiset.card ν))) (u : Fin (Multiset.card ν) →₀ ℕ) (f : Pol K ν) :
    (opΨw P (ρ w) * mulMono u * opE i : Module.End K (Pol K ν)) f =
      Pi.single (w • i) ((opΨw P (ρ w) * mulMono u * opE i : Module.End K (Pol K ν))
        (Pi.single i (f i)) (w • i)) := by
  have h1 : opE i f = Pi.single i (f i) := by
    funext t; rw [opE_apply]; by_cases ht : t = i
    · subst ht; simp
    · rw [ite_eq_right ht, Pi.single_eq_of_ne ht]
  have h2 : mulMono u (Pi.single i (f i)) = (Pi.single i (monomial u 1 * f i) : Pol K ν) := by
    funext t; rw [mulMono_apply]; by_cases ht : t = i
    · subst ht; simp
    · rw [Pi.single_eq_of_ne ht, Pi.single_eq_of_ne ht, mul_zero]
  have h3 : opE i (Pi.single i (f i)) = (Pi.single i (f i) : Pol K ν) := by
    funext t; rw [opE_apply]; by_cases ht : t = i
    · subst ht; simp
    · rw [ite_eq_right ht, Pi.single_eq_of_ne ht]
  rw [Module.End.mul_apply, Module.End.mul_apply, h1, h2, opΨw_single, hρ, Module.End.mul_apply,
    Module.End.mul_apply, h3, h2, opΨw_single, hρ, Pi.single_eq_same]

theorem eqToHom_hom_symm {X Y : ModuleCat.{u} K} (e : X = Y) (x : X) :
    (eqToHom e.symm).hom ((eqToHom e).hom x) = x := by
  rw [← ModuleCat.comp_apply, eqToHom_trans, eqToHom_refl]; rfl

theorem modCast_injective {n : ℕ} {i j : Option (VObj n M)} (e : i = j) :
    Function.Injective (modCast (K := K) e) := by
  subst e; exact fun _ _ h => h

end Aux2

/-! ## The main theorem -/

section Main

variable (K) in
/-- **A `Γ_N`-like functor adapted to `(λ, ν)`** with all blocks of the target paths larger than
`B`: the data of the hypothesis of `linearIndependent_vB`. -/
structure Rep (μ : Wt m₀) (ν : Multiset (Fin m₀)) (ιc : Fin m₀ → Fin M) (dsign : Fin M → K)
    (κ : Fin M → Fin M → K) (B : ℕ) where
  /-- The size of the flag varieties. -/
  N : ℕ
  /-- The functor. -/
  F : (pres (slRootDatum m₀) K).Presented ⥤ ModuleCat.{u} K
  additive : F.Additive
  linear : F.Linear K
  /-- The transformation of diagrams. -/
  ιF : Obj (psig (slRootDatum m₀)) ⥤ Obj (psig (slRootDatum M))
  dnScal : Fin M → Fin M → K
  χ : (psig (slRootDatum M)).Gen → Kˣ
  hF : GammaLike F ιF N dnScal χ
  /-- The rightmost region of the target paths. -/
  μ' : Wt M
  hv : ∀ s : Seq ν, WOK N (ιF.obj (ob (slRootDatum m₀) μ (ups (KLR.Diagram.word s)))).start
    (ιF.obj (ob (slRootDatum m₀) μ (ups (KLR.Diagram.word s)))).word
  he : ∀ s : Seq ν, lastR (ιF.obj (ob (slRootDatum m₀) μ (ups (KLR.Diagram.word s)))).start
    (ιF.obj (ob (slRootDatum m₀) μ (ups (KLR.Diagram.word s)))).word = μ'
  hU : UpCompat ιF ιc μ ν
  hlen : ∀ s : Seq ν, (ιF.obj (ob (slRootDatum m₀) μ (ups (KLR.Diagram.word s)))).word.length =
    Multiset.card ν
  hχd : ∀ c r, (χ (.gen (.dot ⟨(true, c), r⟩)) : K) = dsign c
  hχc : ∀ c d ν', (χ (.gen (.cross true c d ν')) : K) = κ c d
  /-- The units of the bubbles. -/
  ω : Fin m₀ × ℕ → K
  hω : ∀ p, ω p ≠ 0
  hbub : ∀ (s : Seq ν) (p : Fin m₀ × ℕ) q z,
    (F.map (bubAt (slRootDatum m₀) K μ (ups (KLR.Diagram.word s))
      (bubGen (slRootDatum m₀) K μ p.1 (p.2 + 1)))).hom (pv hF μ μ' hv he s q z) =
      pv hF μ μ' hv he s q ((algebraMap K _ (ω p) * bubVal (compOf N μ') (ιc p.1) p.2) * z)
  big : ∀ s : Seq ν, RegionsBig N B (ιF.obj (ob (slRootDatum m₀) μ (ups (KLR.Diagram.word s)))).start
    (ιF.obj (ob (slRootDatum m₀) μ (ups (KLR.Diagram.word s)))).word

attribute [instance] Rep.additive Rep.linear

theorem mkT_C' {D : ℕ} (a : K) : mkT K (wS M) D (C a) = algebraMap K (TrS K M D) a := by
  rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes]

/-- The polynomials `P''` of the conjugated shadow are nonzero. -/
theorem pcc_ne_zero (ιc : Fin m₀ → Fin M) (dsign : Fin M → K)
    (κ : Fin M → Fin M → K) (hd : ∀ c, dsign c * dsign c = 1) (hκ0 : ∀ c d, κ c d ≠ 0)
    (a b : Fin m₀) (_hab : a ≠ b) : Pcc ιc dsign κ a b ≠ 0 := by
  have hda : dsign (ιc a) ≠ 0 := fun h => by simpa [h] using hd (ιc a)
  have hdb : dsign (ιc b) ≠ 0 := fun h => by simpa [h] using hd (ιc b)
  simp only [Pcc, rescaleP, Function.comp_apply, Fc]
  refine mul_ne_zero (by simpa using hκ0 _ _) ?_
  split_ifs
  · simp only [map_sub, aeval_X, Matrix.cons_val_one, Matrix.cons_val_zero]
    intro h
    have := congrArg (fun p : MvPolynomial (Fin 2) K => p.coeff (Finsupp.single 1 1)) h
    rw [coeff_sub, coeff_C_mul, coeff_C_mul, coeff_X, coeff_X, ite_eq_left rfl, ite_eq_right (by
      intro e; have := congrArg (fun f => f 1) e; simp at this), AddMonoidAlgebra.coeff_zero,
      Finsupp.zero_apply] at this
    exact hda (by simpa using this)
  · simp

theorem conj_single_apply {ν : Multiset (Fin m₀)} (d : Fin m₀ → K) (hd : ∀ c, d c * d c = 1)
    (T : Module.End K (Pol K ν)) (i t : Seq ν) (q : MvPolynomial (Fin (Multiset.card ν)) K) :
    ((conjD d * T * conjD d : Module.End K (Pol K ν))
      (Pi.single i (scaleS (fun a => d (i.1 a)) q)) : Pol K ν) t =
      scaleS (fun a => d (t.1 a)) ((T (Pi.single i q) : Pol K ν) t) := by
  have h1 : conjD d (Pi.single i (scaleS (fun a => d (i.1 a)) q)) = (Pi.single i q : Pol K ν) := by
    funext t'
    rw [conjD_apply]
    by_cases ht : t' = i
    · subst ht; rw [Pi.single_eq_same, Pi.single_eq_same, scaleS_scaleS _ (fun a => hd _)]
    · rw [Pi.single_eq_of_ne ht, Pi.single_eq_of_ne ht, map_zero]
  rw [Module.End.mul_apply, Module.End.mul_apply, h1, conjD_apply]

/-- `F(vB p)` on the elements `pv`. -/
theorem map_vB_pv {μ : Wt m₀} {ν : Multiset (Fin m₀)} {ιc : Fin m₀ → Fin M} {dsign : Fin M → K}
    {κ : Fin M → Fin M → K} {B : ℕ} (R : Rep K μ ν ιc dsign κ B) (hιc : Function.Injective ιc)
    (hd : ∀ c, dsign c * dsign c = 1) (hκ : ∀ c, κ c c * dsign c = 1)
    (i j : Seq ν) (b : Seq ν × Equiv.Perm (Fin (Multiset.card ν)) × (Fin (Multiset.card ν) →₀ ℕ))
    (mm : (Fin m₀ × ℕ) →₀ ℕ) (q : MvPolynomial (Fin (Multiset.card ν)) K) :
    letI := R.additive
    (R.F.map (vB (slRootDatum m₀) K μ i j (b, mm))).hom (pv R.hF μ R.μ' R.hv R.he i q 1) =
      pv R.hF μ R.μ' R.hv R.he j ((((conjD (dsign ∘ ιc) * (opΨw (Pcc ιc dsign κ) (ρc ν b.2.1) *
        mulMono b.2.2 * opE b.1) * conjD (dsign ∘ ιc) : Module.End K (Pol K ν)) (Pi.single i q)) :
          Pol K ν) j)
        (bval ιc R.ω (compOf R.N R.μ') mm) := by
  let _ := R.additive
  rw [vB, phi_tmul_apply, R.F.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply,
    map_bubAt_monomial ιc R.ω R.hbub mm i q 1, mul_one]
  exact sh_basis R.hU dsign κ R.hχd R.hχc hιc hd hκ (ρc ν) (hρc ν) b i j q _

set_option backward.isDefEq.respectTransparency false in
theorem toF_injective {S₀ : Signature} {P₀ : Presentation S₀ K} {F : P₀.Presented ⥤ ModuleCat.{u} K}
    {ιF : Obj S₀ ⥤ Obj (psig (slRootDatum M))} {dnScal : Fin M → Fin M → K}
    {χ : (psig (slRootDatum M)).Gen → Kˣ} (hF : GammaLike F ιF N dnScal χ) (a : Obj S₀)
    (ha : WOK N (ιF.obj a).start (ιF.obj a).word) : Function.Injective (hF.toF a ha) := by
  intro y y' h
  have h' := congrArg (eqToHom (hF.obj a)).hom h
  simp only [GammaLike.toF, LinearMap.comp_apply] at h'
  rw [eqToHom_hom_symm, eqToHom_hom_symm] at h'
  exact modCast_injective _ h'

theorem evR_evXi_iotaE (hw : ∀ v, 0 < wS M v) {D : ℕ} (s : Wt M) (ws : List (WCol M))
    (h : WOK N s ws) (Ξs : List (TrS K M D)) (c : Fin (M + 1) → TrS K M D)
    (hp : PathHyp N s ws Ξs c) (μ' : Wt M) (e : lastR s ws = μ') (hd : ∀ j, D ≤ compOf N μ' j)
    (h0 : ∀ j, (sc K (wS M) D (c j)).coeff 0 = 1) (hprod : ∏ j, c j = 1)
    (Q : MvPolynomial ℕ K) (z : H K (compOf N μ')) :
    (evR hw s ws h Ξs c hp).1 (evXi s ws h Q * iotaE s ws h μ' e z) =
      aeval (fun t => Ξs.getD t 0) Q * hLift (compOf N μ') hd c h0 hprod z := by
  rw [map_mul, evR_evXi]
  congr 1
  obtain ⟨hd', h0', hprod', e2⟩ := evR_iotaR N hw s ws h Ξs c hp
    (hCast K (congrArg (compOf N) e.symm) z)
  rw [iotaE, RingHom.comp_apply]
  erw [e2]
  exact hLift_hCast _ _ _ _ _ _ z

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2000000 in
/-- **KL III §6.4, injectivity of `ι'_λ` (abstract form).** Given, for every bound, a `Γ_N`-like
functor as in `Rep`, the elements `ϕ_{ν,λ}(ψ_{ρ w} x^u e_i ⊗ m)_{ij}` (`w • i = j`, `m` a monomial
of `Π_λ`) are linearly independent. -/
theorem linearIndependent_vB (μ : Wt m₀) (ν : Multiset (Fin m₀)) (i j : Seq ν)
    (ιc : Fin m₀ → Fin M) (hιc : Function.Injective ιc) (hlast : ∀ c, (ιc c : ℕ) + 1 < M)
    (dsign : Fin M → K) (κ : Fin M → Fin M → K) (hd : ∀ c, dsign c * dsign c = 1)
    (hκ : ∀ c, κ c c * dsign c = 1) (hκ0 : ∀ c d, κ c d ≠ 0)
    (hrep : ∀ B, Nonempty (Rep K μ ν ιc dsign κ B)) :
    LinearIndependent K (fun p : {p : (Seq ν × Equiv.Perm (Fin (Multiset.card ν)) ×
        (Fin (Multiset.card ν) →₀ ℕ)) × ((Fin m₀ × ℕ) →₀ ℕ) // p.1.1 = i ∧ p.1.2.1 • i = j} =>
      vB (slRootDatum m₀) K μ i j p.1) := by
  classical
  rw [linearIndependent_iff']
  intro S c hsum x0 hx0
  -- The operators of KL I and finitely many test monomials.
  obtain ⟨Op, hOp⟩ : ∃ Op : Equiv.Perm (Fin (Multiset.card ν)) × (Fin (Multiset.card ν) →₀ ℕ) →
      Module.End K (Pol K ν), Op = fun b =>
        opΨw (Pcc ιc dsign κ) (ρc ν b.1) * mulMono b.2 * opE i := ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ G : Equiv.Perm (Fin (Multiset.card ν)) × (Fin (Multiset.card ν) →₀ ℕ) →
      (MvPolynomial (Fin (Multiset.card ν)) K →ₗ[K] MvPolynomial (Fin (Multiset.card ν)) K),
      G = fun b => (LinearMap.proj (R := K)
        (φ := fun _ : Seq ν => MvPolynomial (Fin (Multiset.card ν)) K) j) ∘ₗ Op b ∘ₗ
          LinearMap.single K (fun _ : Seq ν => MvPolynomial (Fin (Multiset.card ν)) K) i :=
    ⟨_, rfl⟩
  obtain ⟨bx, hbx⟩ : ∃ bx : {p : (Seq ν × Equiv.Perm (Fin (Multiset.card ν)) ×
      (Fin (Multiset.card ν) →₀ ℕ)) × ((Fin m₀ × ℕ) →₀ ℕ) // p.1.1 = i ∧ p.1.2.1 • i = j} →
      Equiv.Perm (Fin (Multiset.card ν)) × (Fin (Multiset.card ν) →₀ ℕ),
      bx = fun x => (x.1.1.2.1, x.1.1.2.2) := ⟨_, rfl⟩
  have hOpf : ∀ (b : Equiv.Perm (Fin (Multiset.card ν)) × (Fin (Multiset.card ν) →₀ ℕ)),
      b.1 • i = j → ∀ f : Pol K ν, Op b f = Pi.single j (G b (f i)) := by
    intro b hb f
    have := op_single_apply (Pcc ιc dsign κ) (ρc ν) (fun w => (hρc ν w).2) i b.1 b.2 f
    rw [hb] at this
    rw [hG, hOp]
    exact this
  -- Within a class of bubble monomials, the operators are linearly independent.
  have hgm : ∀ m0 : (Fin m₀ × ℕ) →₀ ℕ,
      LinearIndependent K (fun x : S.filter (fun x => x.1.2 = m0) => G (bx x.1)) := by
    intro m0
    have hinj : Function.Injective (fun x : S.filter (fun x => x.1.2 = m0) =>
        ((i, (bx x.1).1, (bx x.1).2) : Seq ν × Equiv.Perm (Fin (Multiset.card ν)) ×
          (Fin (Multiset.card ν) →₀ ℕ))) := by
      intro x x' h
      simp only [hbx, Prod.mk.injEq] at h
      apply Subtype.ext; apply Subtype.ext
      have e1 := (Finset.mem_filter.1 x.2).2
      have e2 := (Finset.mem_filter.1 x'.2).2
      exact Prod.ext (Prod.ext (x.1.2.1.trans x'.1.2.1.symm) (Prod.ext h.2.1 h.2.2))
        (e1.trans e2.symm)
    have hfull := (linearIndependent_opΨw (k := K) (ν := ν)
      (pcc_ne_zero ιc dsign κ hd hκ0) (ρc ν) (hρc ν)).comp _ hinj
    rw [linearIndependent_iff'] at hfull ⊢
    intro T cb hT b hb
    refine hfull T cb ?_ b hb
    refine LinearMap.ext fun f => ?_
    have hwj' : ∀ x : S.filter (fun x => x.1.2 = m0), (bx x.1).1 • i = j := fun x => by
      rw [hbx]; exact x.1.2.2
    have e1 : ∀ x : S.filter (fun x => x.1.2 = m0),
        (opΨw (Pcc ιc dsign κ) (ρc ν (bx x.1).1) ∘ₗ mulMono (bx x.1).2 ∘ₗ opE i :
        Module.End K (Pol K ν)) f = Pi.single j (G (bx x.1) (f i)) := fun x =>
      by rw [← hOpf (bx x.1) (hwj' x) f, hOp]; rfl
    simp only [Function.comp_apply, LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply,
      e1, LinearMap.zero_apply]
    have e2 : ∑ x ∈ T, cb x • (Pi.single j (G (bx x.1) (f i)) : Pol K ν) =
        Pi.single j ((∑ x ∈ T, cb x • G (bx x.1)) (f i)) := by
      funext t
      rw [Finset.sum_apply]
      by_cases ht : t = j
      · subst ht
        simp [LinearMap.coe_sum, Finset.sum_apply]
      · simp [Pi.single_eq_of_ne ht]
    rw [e2, hT, LinearMap.zero_apply, Pi.single_zero]
  choose Am hAm using fun m0 => exists_finset_separating _ (hgm m0) (fun a => monomial a (1 : K))
    (by rw [← coe_basisMonomials]; exact (basisMonomials _ _).span_eq)
  set A := (S.image (fun x => x.1.2)).biUnion Am with hA_def
  -- The degree bound.
  set dd : Fin m₀ → K := dsign ∘ ιc with hdd
  have hdd' : ∀ c, dd c * dd c = 1 := fun c => hd _
  obtain ⟨scj, hscj⟩ : ∃ f : MvPolynomial (Fin (Multiset.card ν)) K →ₐ[K]
      MvPolynomial (Fin (Multiset.card ν)) K, f = scaleS (fun a => dd (j.1 a)) := ⟨_, rfl⟩
  obtain ⟨sci, hsci⟩ : ∃ f : MvPolynomial (Fin (Multiset.card ν)) K →ₐ[K]
      MvPolynomial (Fin (Multiset.card ν)) K, f = scaleS (fun a => dd (i.1 a)) := ⟨_, rfl⟩
  obtain ⟨Qx, hQx⟩ : ∃ Qx : {p : (Seq ν × Equiv.Perm (Fin (Multiset.card ν)) ×
      (Fin (Multiset.card ν) →₀ ℕ)) × ((Fin m₀ × ℕ) →₀ ℕ) // p.1.1 = i ∧ p.1.2.1 • i = j} →
      (Fin (Multiset.card ν) →₀ ℕ) → MvPolynomial (Fin (Multiset.card ν)) K,
      Qx = fun x a => scj (G (bx x) (monomial a 1)) := ⟨_, rfl⟩
  set E1 := (S ×ˢ A).sup (fun xa => (rename Fin.val (Qx xa.1 xa.2)).totalDegree) with hE1
  set φ' : Fin m₀ × ℕ → VarS M := fun p => Sum.inr (ιc p.1, p.2) with hφ'
  set E2 := S.sup (fun x => Finsupp.weight (wS M) (x.1.2.mapDomain φ')) with hE2
  obtain ⟨R⟩ := hrep (E1 + E2)
  set D := E1 + E2 with hD
  set d := compOf R.N R.μ' with hd_def
  set pos : Fin M → Prop := fun c => 0 ≤ nH d c with hpos_def
  set W := R.ιF.obj (ob (slRootDatum m₀) μ (ups (KLR.Diagram.word j))) with hW
  set Ξs := xiList (K := K) (M := M) (D := D) 0 W.word.length with hΞs
  have hpath : PathHyp R.N W.start W.word Ξs (chernData K M D pos) :=
    pathHyp_of_regionsBig le_rfl (goodData_chernData pos) _ _ 0 (R.big j)
  have hdD : ∀ j', D ≤ d j' := fun j' => by
    have := regionsBig_last _ _ (R.big j) j'
    rw [R.he j] at this
    exact this.le
  set ev := (evR wS_pos W.start W.word (R.hv j) Ξs (chernData K M D pos) hpath).1 with hev
  -- For each test monomial and each bubble monomial, the operators of KL I cancel.
  have key : ∀ a ∈ A, ∀ m0, ∑ x ∈ S.filter (fun x => x.1.2 = m0), c x • G (bx x) (monomial a 1) = 0 := by
    intro a ha m0
    -- 1. `F` of the relation, on the test vector.
    have h1 : ∑ x ∈ S, c x • pv R.hF μ R.μ' R.hv R.he j (Qx x a) (bval ιc R.ω d x.1.2) = 0 := by
      have := congrArg (fun φ => ((R.F.mapLinearMap K) φ).hom
        (pv R.hF μ R.μ' R.hv R.he i (sci (monomial a 1)) 1)) hsum
      simp only [map_sum, map_smul, map_zero, ModuleCat.hom_sum, ModuleCat.hom_smul,
        LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply, ModuleCat.hom_zero,
        LinearMap.zero_apply, Functor.coe_mapLinearMap] at this
      refine Eq.trans ?_ this
      refine Finset.sum_congr rfl fun x _ => ?_
      congr 1
      have hx1 : x.1 = ((i, x.1.1.2.1, x.1.1.2.2), x.1.2) := Prod.ext (Prod.ext x.2.1 rfl) rfl
      rw [hx1, hsci, map_vB_pv R hιc hd hκ i j _ x.1.2, conj_single_apply dd hdd', hQx, hbx, hscj,
        hG, hOp]
      rfl
    -- 2. In the path bimodule of `E_j 1_λ`.
    have h2 : ∑ x ∈ S, c x • (show RT (gammaR K R.N W.start W.word (R.hv j)) from
        evXi W.start W.word (R.hv j) (rename Fin.val (Qx x a)) *
        iotaE W.start W.word (R.hv j) R.μ' (R.he j) (bval ιc R.ω d x.1.2)) = 0 := by
      apply toF_injective R.hF _ (R.hv j)
      rw [map_sum, map_zero]
      rw [← h1]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [map_smul]
      rfl
    -- 3. The evaluation into the truncated polynomial ring.
    have h3 := congrArg ev h2
    rw [map_sum, map_zero] at h3
    set φ'' : Fin m₀ × ℕ → Fin M × ℕ := fun p => (ιc p.1, p.2) with hφ''
    set sx : ((Fin m₀ × ℕ) →₀ ℕ) → K := fun mm => mm.prod fun p e => (R.ω p * (-1) ^ (p.2 + 1)) ^ e
      with hsx
    have hterm : ∀ x ∈ S, ev (c x • (show RT (gammaR K R.N W.start W.word (R.hv j)) from
        evXi W.start W.word (R.hv j) (rename Fin.val (Qx x a)) *
        iotaE W.start W.word (R.hv j) R.μ' (R.he j) (bval ιc R.ω d x.1.2))) =
        mkT K (wS M) D (rename Sum.inl (rename Fin.val (Qx x a)) *
          monomial ((x.1.2.mapDomain φ'').mapDomain Sum.inr) (c x * sx x.1.2)) := by
      intro x _
      rw [RT.smul_def, map_mul, hev, evR_right, ← hev, hev,
        evR_evXi_iotaE wS_pos W.start W.word (R.hv j) Ξs (chernData K M D pos) hpath R.μ' (R.he j)
          hdD (coeff_sc_chernData pos) (prod_chernData pos),
        aeval_rename_val (by rw [R.hlen j]), hLift_bval pos ιc hlast R.ω d hdD (fun c => Iff.rfl)]
      rw [show (monomial ((x.1.2.mapDomain φ'').mapDomain Sum.inr) (c x * sx x.1.2) :
          MvPolynomial (VarS M) K) = C (c x) * C (sx x.1.2) *
            monomial (x.1.2.mapDomain fun p => (Sum.inr (ιc p.1, p.2) : VarS M)) 1 by
        rw [← Finsupp.mapDomain_comp, mul_assoc, C_mul_monomial, mul_one, C_mul_monomial]
        rfl]
      simp only [map_mul, mkT_C', hsx]
      ring
    rw [Finset.sum_congr rfl hterm, ← map_sum] at h3
    -- 4. The polynomial vanishes (all its monomials have weight `≤ D`).
    have h4 : (∑ x ∈ S, rename Sum.inl (rename Fin.val (Qx x a)) *
        monomial ((x.1.2.mapDomain φ'').mapDomain Sum.inr) (c x * sx x.1.2)) = 0 := by
      refine eq_zero_of_mkT_eq_zero (fun s hs => ?_) h3
      have hs' := MvPolynomial.support_sum hs
      rw [Finset.mem_biUnion] at hs'
      obtain ⟨x, hx, hsx'⟩ := hs'
      refine le_trans (weight_support_le _ _ _ s hsx') (Nat.add_le_add ?_ ?_)
      · have := Finset.le_sup (f := fun xa : {p : (Seq ν × Equiv.Perm (Fin (Multiset.card ν)) ×
          (Fin (Multiset.card ν) →₀ ℕ)) × ((Fin m₀ × ℕ) →₀ ℕ) // p.1.1 = i ∧ p.1.2.1 • i = j} ×
          (Fin (Multiset.card ν) →₀ ℕ) => (rename Fin.val (Qx xa.1 xa.2)).totalDegree)
          (b := (x, a)) (Finset.mem_product.2 ⟨hx, ha⟩)
        exact this
      · have := Finset.le_sup (f := fun x : {p : (Seq ν × Equiv.Perm (Fin (Multiset.card ν)) ×
          (Fin (Multiset.card ν) →₀ ℕ)) × ((Fin m₀ × ℕ) →₀ ℕ) // p.1.1 = i ∧ p.1.2.1 • i = j} =>
          Finsupp.weight (wS M) (x.1.2.mapDomain φ')) hx
        rw [← Finsupp.mapDomain_comp]
        exact this
    -- 5. Separating the bubble monomials.
    have h5 := sum_eq_zero_of_classes S (fun x => c x * sx x.1.2)
      (fun x => rename Fin.val (Qx x a)) (fun x => x.1.2.mapDomain φ'') h4 (m0.mapDomain φ'')
    have hinj : Function.Injective (Finsupp.mapDomain (M := ℕ) φ'') := by
      refine Finsupp.mapDomain_injective fun p p' h => ?_
      simp only [hφ'', Prod.mk.injEq] at h
      exact Prod.ext (hιc h.1) h.2
    have hfilt : S.filter (fun x => x.1.2.mapDomain φ'' = m0.mapDomain φ'') =
        S.filter (fun x => x.1.2 = m0) := Finset.filter_congr fun x _ => hinj.eq_iff
    rw [hfilt] at h5
    have hs0 : sx m0 ≠ 0 := by
      rw [hsx]
      simp only
      rw [Finsupp.prod, Finset.prod_ne_zero_iff]
      intro p _
      exact pow_ne_zero _ (mul_ne_zero (R.hω p) (pow_ne_zero _ (by norm_num)))
    have h6 : sx m0 • rename Fin.val (∑ x ∈ S.filter (fun x => x.1.2 = m0), c x • Qx x a) = 0 := by
      rw [map_sum, Finset.smul_sum, ← h5]
      refine Finset.sum_congr rfl fun x hx => ?_
      rw [(Finset.mem_filter.1 hx).2, map_smul, smul_smul, mul_comm]
    have h7 : ∑ x ∈ S.filter (fun x => x.1.2 = m0), c x • Qx x a = 0 :=
      rename_injective _ Fin.val_injective (by rw [map_zero]; exact (smul_eq_zero.1 h6).resolve_left hs0)
    have hinv : ∀ q, scj (scj q) = q := fun q => by
      rw [hscj]; exact scaleS_scaleS _ (fun a => hdd' _) q
    calc ∑ x ∈ S.filter (fun x => x.1.2 = m0), c x • G (bx x) (monomial a 1)
        = scj (∑ x ∈ S.filter (fun x => x.1.2 = m0), c x • Qx x a) := by
          rw [map_sum]
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [AlgHom.map_smul_of_tower, hQx]
          exact (congrArg (c x • ·) (hinv _)).symm
      _ = 0 := by rw [h7, map_zero]
  -- Conclusion: the coefficients of the class of `x0` vanish.
  have hmem : Am x0.1.2 ⊆ A := fun a ha => Finset.mem_biUnion.2
    ⟨x0.1.2, Finset.mem_image_of_mem _ hx0, ha⟩
  have hc0 := hAm x0.1.2 (fun x => c x.1) (fun a ha => by
    rw [← key a (hmem ha) x0.1.2, ← Finset.sum_coe_sort (S.filter (fun x => x.1.2 = x0.1.2))])
  exact congrFun hc0 ⟨x0, Finset.mem_filter.2 ⟨hx0, rfl⟩⟩

end Main

end Categorification.Flag.Indep

end
