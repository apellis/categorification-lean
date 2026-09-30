/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Flag.GammaIndepFunctor
import Categorification.Flag.GammaIndepConj
import Categorification.Diagrams.KL3.SpanningPhi

/-!
# `R(ν)` acting through a `Γ_N`-like functor: the polynomial shadow

Khovanov–Lauda III (arXiv:0807.3250v1), §6.4 (TeX `sln-2008-ArXiv.tex` l. 9598–9790): "the action
on `Pol_ν(ξ)` given by the 2-functor `Γ^G` coincides with the action of `R(ν)` on `Pol_ν` defined
in [KL]. In particular, bimodule maps `f_D` corresponding to basis elements of `R(ν)` must act by
linear independent operators".

Let `F` be a `Γ_N`-like functor out of `U` (`GammaLike`), sending the upward generators of `U`
(for the colours of `ν`) to single upward generators of `Flag_N` (`UpCompat`), with units `d_c`
on dots and `κ_{cd}` on crossings. For the matrix of 2-morphisms `toUEnd r` (`r ∈ R(ν)`,
KL III §3.2.2) we prove (`Sh`): on the elements `pv s q z = evXi q * iotaE z` of `F(E_s 1_μ)`
(a polynomial `q` in the dots times an element `z` of the rightmost region),
`F(toUEnd r)_{s s'}` acts by an operator `T` of the polynomial representation, namely

* the idempotent `e_i`: `opE i`;
* the dot `x_a`: `opXd` (rescaled by `d_c`), the crossing `ψ_j`: `opΨκ` (rescaled by `κ_{cd}`,
  with the polynomials `Fc` of `Γ_N`, KL III (6.8));
* the basis element `ψ_{ρ w} x^u e_i` of KL II (`Categorification.KLR.KL2.basis`):
  `conjD ∘ (opΨw P'' (ρ w) ∘ mulMono u ∘ opE i) ∘ conjD` (`sh_basis`), which is the operator of
  KL I's polynomial representation for the polynomials `P'' = rescaleP` conjugated by the
  involution `conjD`.
-/

noncomputable section

namespace Categorification.Flag.Indep

open Categorification.Flag Categorification.KL3.Diagram StringDiagrams CategoryTheory
  Categorification.KLR Categorification.KLR.PolyRep MvPolynomial

universe u

variable {K : Type u} [Field K] {m₀ M N : ℕ}


/-- The compatibility of `ιF` with the upward generators of colours in `ν`. -/
structure UpCompat (ιF : Obj (psig (slRootDatum m₀)) ⥤ Obj (psig (slRootDatum M))) (ιc : Fin m₀ → Fin M)
    (μ : Wt m₀) (ν : Multiset (Fin m₀)) : Prop where
  dot : ∀ (s : Seq ν) (a : Fin (Multiset.card ν)), ∃ L : Layer (psig (slRootDatum M)),
    Diagram.layers (ιF.map (upDiag (slRootDatum m₀) μ (KLR.Diagram.dotD s a))) = [L] ∧ L.left.length = a ∧
      ∃ r, L.gen = .gen (.dot ⟨(true, ιc (s.1 a)), r⟩)
  cross : ∀ (s : Seq ν) (j : ℕ) (h : j + 1 < Multiset.card ν), ∃ L : Layer (psig (slRootDatum M)),
    Diagram.layers (ιF.map (upDiag (slRootDatum m₀) μ (KLR.Diagram.crossD s h))) = [L] ∧ L.left.length = j ∧
      ∃ ν', L.gen = .gen (.cross true (ιc (s.1 ⟨j, by omega⟩)) (ιc (s.1 ⟨j + 1, h⟩)) ν')

variable {F : (pres (slRootDatum m₀) K).Presented ⥤ ModuleCat.{u} K}
  {ιF : Obj (psig (slRootDatum m₀)) ⥤ Obj (psig (slRootDatum M))}
  {dnScal : Fin M → Fin M → K} {χ : (psig (slRootDatum M)).Gen → Kˣ}
  (hF : GammaLike F ιF N dnScal χ) {ν : Multiset (Fin m₀)} (μ : Wt m₀) (μ' : Wt M)
  (hv : ∀ s : Seq ν, WOK N (ιF.obj (ob (slRootDatum m₀) μ (ups (KLR.Diagram.word s)))).start
    (ιF.obj (ob (slRootDatum m₀) μ (ups (KLR.Diagram.word s)))).word)
  (he : ∀ s : Seq ν, lastR (ιF.obj (ob (slRootDatum m₀) μ (ups (KLR.Diagram.word s)))).start
    (ιF.obj (ob (slRootDatum m₀) μ (ups (KLR.Diagram.word s)))).word = μ')


/-- The elements `evXi q * iotaE z` of `F(E_s 1_μ)`, for polynomials in the variables of
`Pol_ν`. -/
def pv (s : Seq ν) (q : MvPolynomial (Fin (Multiset.card ν)) K) (z : H K (compOf N μ')) :
    F.obj ((pres (slRootDatum m₀) K).obj (ob (slRootDatum m₀) μ (ups (KLR.Diagram.word s)))) :=
  hF.pvec _ (hv s) μ' (he s) (rename Fin.val q) z

theorem pv_zero (s : Seq ν) (z : H K (compOf N μ')) : pv hF μ μ' hv he s 0 z = 0 := by
  rw [pv, map_zero, GammaLike.pvec_zero]

theorem pv_add (s : Seq ν) (q q' : MvPolynomial (Fin (Multiset.card ν)) K) (z : H K (compOf N μ')) :
    pv hF μ μ' hv he s (q + q') z = pv hF μ μ' hv he s q z + pv hF μ μ' hv he s q' z := by
  rw [pv, map_add, GammaLike.pvec_add]; rfl

theorem pv_sum (s : Seq ν) {ι : Type*} (S : Finset ι) (q : ι → MvPolynomial (Fin (Multiset.card ν)) K)
    (z : H K (compOf N μ')) :
    pv hF μ μ' hv he s (∑ x ∈ S, q x) z = ∑ x ∈ S, pv hF μ μ' hv he s (q x) z := by
  classical
  induction S using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, pv_zero]
  | @insert x S hx ih => rw [Finset.sum_insert hx, Finset.sum_insert hx, pv_add, ih]

theorem pv_smul (s : Seq ν) (c : K) (q : MvPolynomial (Fin (Multiset.card ν)) K) (z : H K (compOf N μ')) :
    pv hF μ μ' hv he s (C c * q) z = c • pv hF μ μ' hv he s q z := by
  rw [pv, map_mul, rename_C, GammaLike.pvec_smul]; rfl

/-- **`F ∘ A` has polynomial shadow `T`** on the elements `pv`. -/
def Sh (A : KLR.Diagram.MatEnd (fun s : Seq ν => (pres (slRootDatum m₀) K).obj (ob (slRootDatum m₀) μ (ups (KLR.Diagram.word s)))))
    (T : Module.End K (Pol K ν)) : Prop :=
  ∀ s s' q z, (F.map (A s s')).hom (pv hF μ μ' hv he s q z) =
    pv hF μ μ' hv he s' ((T (Pi.single s q)) s') z

variable {hF μ μ' hv he}

theorem Sh.mul [F.Additive] {A B : KLR.Diagram.MatEnd (fun s : Seq ν => (pres (slRootDatum m₀) K).obj (ob (slRootDatum m₀) μ (ups (KLR.Diagram.word s))))}
    {T T' : Module.End K (Pol K ν)} (hA : Sh hF μ μ' hv he A T) (hB : Sh hF μ μ' hv he B T') :
    Sh hF μ μ' hv he (A * B) (T * T') := by
  intro s l q z
  have key : ∀ x, (F.map (B s x ≫ A x l)).hom (pv hF μ μ' hv he s q z) =
      pv hF μ μ' hv he l ((T (Pi.single x ((T' (Pi.single s q)) x))) l) z := fun x => by
    rw [F.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply, hB, hA]
  rw [KLR.Diagram.MatEnd.mul_apply, F.map_sum, ModuleCat.hom_sum, LinearMap.coe_sum,
    Finset.sum_apply]
  simp only [key]
  rw [← pv_sum]
  congr 1
  rw [Module.End.mul_apply]
  conv_rhs => rw [← Finset.univ_sum_single (T' (Pi.single s q))]
  rw [map_sum, Finset.sum_apply]

theorem sh_one [F.Additive] : Sh hF μ μ' hv he 1 1 := by
  intro s s' q z
  by_cases h : s = s'
  · subst h
    rw [KLR.Diagram.MatEnd.one_apply_self, F.map_id, ModuleCat.hom_id, LinearMap.id_apply,
      Module.End.one_apply, Pi.single_eq_same]
  · rw [KLR.Diagram.MatEnd.one_apply_of_ne h, F.map_zero, ModuleCat.hom_zero, LinearMap.zero_apply,
      Module.End.one_apply, Pi.single_eq_of_ne (Ne.symm h), pv_zero]

theorem Sh.pow [F.Additive] {A : KLR.Diagram.MatEnd (fun s : Seq ν => (pres (slRootDatum m₀) K).obj (ob (slRootDatum m₀) μ (ups (KLR.Diagram.word s))))}
    {T : Module.End K (Pol K ν)} (hA : Sh hF μ μ' hv he A T) :
    ∀ n : ℕ, Sh hF μ μ' hv he (A ^ n) (T ^ n)
  | 0 => by rw [pow_zero, pow_zero]; exact sh_one
  | n + 1 => by rw [pow_succ, pow_succ]; exact (Sh.pow hA n).mul hA

/-- Shadows of sums of matrix units. -/
theorem sh_sum_single [F.Additive] (g : Seq ν → Seq ν)
    (f : ∀ s, (pres (slRootDatum m₀) K).obj (ob (slRootDatum m₀) μ (ups (KLR.Diagram.word s))) ⟶
      (pres (slRootDatum m₀) K).obj (ob (slRootDatum m₀) μ (ups (KLR.Diagram.word (g s)))))
    (T : Module.End K (Pol K ν))
    (h1 : ∀ s q z, (F.map (f s)).hom (pv hF μ μ' hv he s q z) =
      pv hF μ μ' hv he (g s) ((T (Pi.single s q)) (g s)) z)
    (h2 : ∀ s q t', t' ≠ g s → (T (Pi.single s q)) t' = 0) :
    Sh hF μ μ' hv he (∑ s, KLR.Diagram.MatEnd.single s (g s) (f s)) T := by
  intro t t' q z
  rw [KLR.Diagram.MatEnd.sum_apply, Finset.sum_eq_single t]
  · by_cases ht : t' = g t
    · subst ht
      rw [KLR.Diagram.MatEnd.single_apply_self]
      exact h1 t q z
    · rw [KLR.Diagram.MatEnd.single_apply_of_ne _ (fun h => ht h.2), F.map_zero, ModuleCat.hom_zero,
        LinearMap.zero_apply, h2 t q t' ht, pv_zero]
  · intro s _ hs
    exact KLR.Diagram.MatEnd.single_apply_of_ne _ (fun h => hs h.1.symm)
  · intro h; exact absurd (Finset.mem_univ _) h

/-! ## The generators -/

variable {ιc : Fin m₀ → Fin M} (hU : UpCompat ιF ιc μ ν) (dsign : Fin M → K) (κ : Fin M → Fin M → K)
  (hχd : ∀ c r, (χ (.gen (.dot ⟨(true, c), r⟩)) : K) = dsign c)
  (hχc : ∀ c d ν', (χ (.gen (.cross true c d ν')) : K) = κ c d)

set_option backward.isDefEq.respectTransparency false in
include hU hχd in
theorem sh_dotE (s : Seq ν) (a : Fin (Multiset.card ν)) (q : MvPolynomial (Fin (Multiset.card ν)) K) (z : H K (compOf N μ')) :
    (F.map ((upFunctor (slRootDatum m₀) K μ).map (KLR.Diagram.dotE K (KLR.klQ2 K (slCartan m₀)) s a))).hom
      (pv hF μ μ' hv he s q z) = pv hF μ μ' hv he s (C (dsign (ιc (s.1 a))) * X a * q) z := by
  obtain ⟨L, hL, hlen, r, hg⟩ := hU.dot s a
  have hS : ∀ hd hc (e₁ : lastR (ιF.obj _).start (L.left ++ gdom L.gen ++ L.right) = μ')
      (e₂ : lastR (ιF.obj _).start (L.left ++ gcod L.gen ++ L.right) = μ'),
      Shadow μ' e₁ e₂ (layerMap K N (ιF.obj (ob (slRootDatum m₀) μ (ups (KLR.Diagram.word s)))).start
        L.left L.gen L.right hd hc) (fun q => X L.left.length * q) := by
    obtain ⟨st, left, gen, right⟩ := L
    simp only at hg
    subst hg
    exact fun hd hc e₁ e₂ => shadow_dotLayer _ _ left right hd hc e₁ e₂
  have hgs : genScal K dnScal L.gen = 1 := by rw [hg]; rfl
  have hm := GammaLike.map_pvec hF (upDiag (slRootDatum m₀) μ (KLR.Diagram.dotD s a)) L hL (hv s)
    (hv s) (he s) (he s) hS hgs (rename Fin.val q) z
  rw [KLR.Diagram.dotE, upFunctor_diag]
  refine hm.trans ?_
  rw [hg, hχd, pv, ← GammaLike.pvec_smul]
  congr 1
  rw [hlen, map_mul, map_mul, rename_X, rename_C, ← mul_assoc]

/-- The operators of KL I §2.3 with the polynomials of `Γ_N` (KL III (6.8)) are the shadows of
the crossings, after renaming the variables `Fin n → ℕ`. -/
theorem rename_crossComp {ιc : Fin m₀ → Fin M} (hιc : Function.Injective ιc)
    {ν : Multiset (Fin m₀)} (s : Seq ν) (j : ℕ) (h : j + 1 < Multiset.card ν)
    (q : MvPolynomial (Fin (Multiset.card ν)) K) :
    rename Fin.val (crossComp (fun c d => Fc K (ιc c) (ιc d)) j h s q) =
      opCross (ιc (s.1 ⟨j, by omega⟩)) (ιc (s.1 ⟨j + 1, h⟩)) j (rename Fin.val q) := by
  unfold crossComp opCross
  by_cases hc : s.lbl ⟨j, by omega⟩ = s.lbl ⟨j + 1, h⟩
  · have hc' : s.1 ⟨j, by omega⟩ = s.1 ⟨j + 1, h⟩ := hc
    rw [ite_eq_left hc, ite_eq_left (congrArg ιc hc'), LinearMap.coe_mk]
    exact rename_ddiff Fin.val_injective (by simp [Fin.ext_iff]) q
  · have hc' : ¬ ιc (s.1 ⟨j, by omega⟩) = ιc (s.1 ⟨j + 1, h⟩) := fun e => hc (hιc e)
    rw [ite_eq_right hc, ite_eq_right hc']
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.mulLeft_apply,
      AlgHom.toLinearMap_apply, map_mul, rename_rename]
    have e1 : (Fin.val ∘ ![(⟨j, by omega⟩ : Fin (Multiset.card ν)), ⟨j + 1, h⟩]) = ![j, j + 1] := by
      funext x; fin_cases x <;> rfl
    have e2 : (Fin.val ∘ ⇑(TypeA.sadj (Multiset.card ν) j)) =
        ⇑(Equiv.swap j (j + 1)) ∘ Fin.val := by
      funext x
      simp only [Function.comp_apply]
      rw [TypeA.sadj_val_of_lt h]
      unfold TypeA.swapNat
      split_ifs with h1 h2
      · rw [h1, Equiv.swap_apply_left]
      · rw [h2, Equiv.swap_apply_right]
      · rw [Equiv.swap_apply_of_ne_of_ne h1 h2]
    rw [e1, e2]

variable (hιc : Function.Injective ιc)

set_option backward.isDefEq.respectTransparency false in
include hU hχc hιc in
theorem sh_crossE (s : Seq ν) (j : ℕ) (h : j + 1 < Multiset.card ν)
    (q : MvPolynomial (Fin (Multiset.card ν)) K) (z : H K (compOf N μ')) :
    (F.map ((upFunctor (slRootDatum m₀) K μ).map
      (KLR.Diagram.crossE K (KLR.klQ2 K (slCartan m₀)) s j))).hom (pv hF μ μ' hv he s q z) =
      pv hF μ μ' hv he (TypeA.sadj (Multiset.card ν) j • s)
        (C (κ (ιc (s.1 ⟨j, by omega⟩)) (ιc (s.1 ⟨j + 1, h⟩))) *
          crossComp (fun c d => Fc K (ιc c) (ιc d)) j h s q) z := by
  obtain ⟨L, hL, hlen, ν', hg⟩ := hU.cross s j h
  have hS : ∀ hd hc (e₁ : lastR (ιF.obj _).start (L.left ++ gdom L.gen ++ L.right) = μ')
      (e₂ : lastR (ιF.obj _).start (L.left ++ gcod L.gen ++ L.right) = μ'),
      Shadow μ' e₁ e₂ (layerMap K N (ιF.obj (ob (slRootDatum m₀) μ (ups (KLR.Diagram.word s)))).start
        L.left L.gen L.right hd hc)
        (opCross (ιc (s.1 ⟨j, by omega⟩)) (ιc (s.1 ⟨j + 1, h⟩)) L.left.length) := by
    obtain ⟨st, left, gen, right⟩ := L
    simp only at hg
    subst hg
    exact fun hd hc e₁ e₂ => shadow_crossLayer _ _ _ _ left right hd hc e₁ e₂
  have hgs : genScal K dnScal L.gen = 1 := by rw [hg]; rfl
  have hm := GammaLike.map_pvec hF (upDiag (slRootDatum m₀) μ (KLR.Diagram.crossD s h)) L hL (hv s)
    (hv _) (he s) (he _) hS hgs (rename Fin.val q) z
  rw [KLR.Diagram.crossE_def _ h, upFunctor_diag]
  refine hm.trans ?_
  rw [hg, hχc, pv, ← GammaLike.pvec_smul, hlen, map_mul, rename_C, rename_crossComp hιc]
  rfl

theorem sh_toUEnd_e [F.Additive] (i : Seq ν) :
    Sh hF μ μ' hv he (toUEnd (slRootDatum m₀) K μ ν (KLRAlgebra.e i)) (opE i) := by
  rw [toUEnd_e, show KLR.Diagram.MatEnd.single i i (𝟙 _) =
    ∑ s, KLR.Diagram.MatEnd.single s s (if s = i then 𝟙 _ else 0) from ?_]
  · refine sh_sum_single id _ _ (fun s q z => ?_) (fun s q t' ht => ?_)
    · simp only [id]
      split_ifs with hs
      · subst hs
        rw [F.map_id, ModuleCat.hom_id, LinearMap.id_apply, opE_apply, ite_eq_left rfl,
          Pi.single_eq_same]
      · rw [F.map_zero, ModuleCat.hom_zero, LinearMap.zero_apply, opE_apply, ite_eq_right hs, pv_zero]
    · rw [opE_apply]
      split_ifs with h
      · subst h; exact Pi.single_eq_of_ne ht _
      · rfl
  · rw [Finset.sum_eq_single i (fun s _ hs => by rw [ite_eq_right hs, KLR.Diagram.MatEnd.single_zero])
      (fun h => absurd (Finset.mem_univ _) h), ite_eq_left rfl]

set_option backward.isDefEq.respectTransparency false in
include hU hχd in
theorem sh_toUEnd_x [F.Additive] (a : Fin (Multiset.card ν)) :
    Sh hF μ μ' hv he (toUEnd (slRootDatum m₀) K μ ν (KLRAlgebra.x a)) (opXd (dsign ∘ ιc) a) := by
  rw [toUEnd_x]
  refine sh_sum_single id _ _ (fun s q z => ?_) (fun s q t' ht => ?_)
  · refine (sh_dotE hU dsign hχd s a q z).trans ?_
    simp only [id, opXd_apply, Function.comp_apply, Pi.single_eq_same]
  · rw [opXd_apply, Pi.single_eq_of_ne (show t' ≠ s from ht), mul_zero]

set_option backward.isDefEq.respectTransparency false in
include hU hχc hιc in
theorem sh_toUEnd_ψ [F.Additive] (j : ℕ) :
    Sh hF μ μ' hv he (toUEnd (slRootDatum m₀) K μ ν (KLRAlgebra.ψ j))
      (opΨκ (fun c d => κ (ιc c) (ιc d)) (fun c d => Fc K (ιc c) (ιc d)) j) := by
  rw [toUEnd_ψ]
  refine sh_sum_single (fun s => TypeA.sadj (Multiset.card ν) j • s) _ _ (fun s q z => ?_)
    (fun s q t' ht => ?_)
  · by_cases h : j + 1 < Multiset.card ν
    · refine (sh_crossE hU κ hχc hιc s j h q z).trans ?_
      rw [opΨκ, dite_eq_left h]
      simp only [LinearMap.pi_apply, LinearMap.smul_apply, LinearMap.comp_apply,
        LinearMap.proj_apply, sadj_smul_sadj_smul', Pi.single_eq_same, smul_eq_C_mul]
    · rw [KLR.Diagram.crossE_of_le _ (by omega), Functor.map_zero, F.map_zero, ModuleCat.hom_zero,
        LinearMap.zero_apply, opΨκ, dite_eq_right h, LinearMap.zero_apply, Pi.zero_apply, pv_zero]
  · unfold opΨκ
    split_ifs with h
    · simp only [LinearMap.pi_apply, LinearMap.smul_apply, LinearMap.comp_apply,
        LinearMap.proj_apply]
      rw [Pi.single_eq_of_ne (fun e => ht (by rw [← e, sadj_smul_sadj_smul'])), map_zero,
        smul_zero]
    · rfl

theorem opX_pow_apply {ν : Multiset (Fin m₀)} (a : Fin (Multiset.card ν)) (n : ℕ) (f : Pol K ν)
    (t : Seq ν) : ((opX a : Module.End K (Pol K ν)) ^ n) f t = X a ^ n * f t := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', Module.End.mul_apply, opX_apply, ih, pow_succ', mul_assoc]

theorem mulMono_single_add {ν : Multiset (Fin m₀)} (a : Fin (Multiset.card ν)) (n : ℕ)
    (u : Fin (Multiset.card ν) →₀ ℕ) :
    (mulMono (Finsupp.single a n + u) : Module.End K (Pol K ν)) = opX a ^ n * mulMono u := by
  refine LinearMap.ext fun f => funext fun t => ?_
  rw [mulMono_apply, Module.End.mul_apply, opX_pow_apply, mulMono_apply, monomial_single_add,
    mul_assoc]

theorem conj_mul_conj {d : Fin m₀ → K} (hd : ∀ c, d c * d c = 1) {ν : Multiset (Fin m₀)}
    (A B : Module.End K (Pol K ν)) :
    (conjD d * A * conjD d) * (conjD d * B * conjD d) = conjD d * (A * B) * conjD d := by
  have h := conjD_conjD (ν := ν) d hd
  calc (conjD d * A * conjD d) * (conjD d * B * conjD d)
      = conjD d * A * (conjD d * conjD d) * B * conjD d := by noncomm_ring
    _ = conjD d * (A * B) * conjD d := by rw [h]; noncomm_ring

theorem conj_pow {d : Fin m₀ → K} (hd : ∀ c, d c * d c = 1) {ν : Multiset (Fin m₀)}
    (A : Module.End K (Pol K ν)) :
    ∀ n : ℕ, conjD d * A ^ n * conjD d = (conjD d * A * conjD d) ^ n
  | 0 => by rw [pow_zero, pow_zero, mul_one, conjD_conjD _ hd]
  | n + 1 => by rw [pow_succ, pow_succ, ← conj_pow hd A n, conj_mul_conj hd]

variable (hd : ∀ c, dsign c * dsign c = 1) (hκ : ∀ c, κ c c * dsign c = 1)

/-- The polynomials of the conjugated shadow of the crossings. -/
abbrev Pcc (ιc : Fin m₀ → Fin M) (dsign : Fin M → K) (κ : Fin M → Fin M → K) :
    Fin m₀ → Fin m₀ → MvPolynomial (Fin 2) K :=
  rescaleP (dsign ∘ ιc) (fun c d => κ (ιc c) (ιc d)) (fun c d => Fc K (ιc c) (ιc d))

include hU hχc hιc hd hκ in
theorem sh_ψw [F.Additive] (ρ : List ℕ) :
    Sh hF μ μ' hv he (toUEnd (slRootDatum m₀) K μ ν (KLRAlgebra.ψw ρ))
      (conjD (dsign ∘ ιc) * opΨw (Pcc ιc dsign κ) ρ * conjD (dsign ∘ ιc)) := by
  have hd' : ∀ c, (dsign ∘ ιc) c * (dsign ∘ ιc) c = 1 := fun c => hd _
  induction ρ with
  | nil =>
    rw [KLRAlgebra.ψw, List.map_nil, List.prod_nil, map_one, opΨw_nil, mul_one,
      conjD_conjD _ hd']
    exact sh_one
  | cons j ρ ih =>
    rw [KLRAlgebra.ψw, List.map_cons, List.prod_cons, map_mul, opΨw_cons, ← conj_mul_conj hd']
    refine Sh.mul ?_ ih
    have h := conjD_opΨκ (ν := ν) (dsign ∘ ιc) (fun c d => κ (ιc c) (ιc d)) hd' (fun c => hκ _)
      (fun c d => Fc K (ιc c) (ιc d)) j
    rw [← h, ← mul_assoc, ← mul_assoc, conjD_conjD _ hd', one_mul, mul_assoc, conjD_conjD _ hd',
      mul_one]
    exact sh_toUEnd_ψ hU κ hχc hιc j

include hU hχd hd in
theorem sh_mono [F.Additive] (u : Fin (Multiset.card ν) →₀ ℕ) :
    Sh hF μ μ' hv he (toUEnd (slRootDatum m₀) K μ ν (KLRAlgebra.pol (monomial u 1)))
      (conjD (dsign ∘ ιc) * mulMono u * conjD (dsign ∘ ιc)) := by
  have hd' : ∀ c, (dsign ∘ ιc) c * (dsign ∘ ιc) c = 1 := fun c => hd _
  induction u using Finsupp.induction with
  | zero =>
    have hm : (mulMono (0 : Fin (Multiset.card ν) →₀ ℕ) : Module.End K (Pol K ν)) = 1 := by
      refine LinearMap.ext fun f => funext fun t => ?_
      rw [mulMono_apply, monomial_zero', C_1, one_mul]; rfl
    rw [monomial_zero', C_1, map_one, map_one, hm, mul_one, conjD_conjD _ hd']
    exact sh_one
  | single_add a n u _ _ ih =>
    rw [monomial_single_add, map_mul, map_pow, KLRAlgebra.pol_X, map_mul, map_pow,
      mulMono_single_add, ← conj_mul_conj hd']
    refine Sh.mul ?_ ih
    have hx := conjD_opXd (ν := ν) (dsign ∘ ιc) hd' a
    have hp : conjD (dsign ∘ ιc) * (opX a : Module.End K (Pol K ν)) ^ n * conjD (dsign ∘ ιc) =
        (opXd (dsign ∘ ιc) a) ^ n := by
      rw [conj_pow hd', ← hx, ← mul_assoc, ← mul_assoc, conjD_conjD _ hd', one_mul, mul_assoc,
        conjD_conjD _ hd', mul_one]
    rw [hp]
    exact (sh_toUEnd_x hU dsign hχd a).pow n

include hU hχc hχd hιc hd hκ in
/-- **The shadow of a basis element of `R(ν)`** (KL II basis `ψ_{ρ w} x^u e_i`). -/
theorem sh_basis [F.Additive] (ρ : Equiv.Perm (Fin (Multiset.card ν)) → List ℕ)
    (hρ : ∀ w, TypeA.IsReduced (Multiset.card ν) (ρ w) ∧
      TypeA.wordProd (Multiset.card ν) (ρ w) = w)
    (b : Seq ν × Equiv.Perm (Fin (Multiset.card ν)) × (Fin (Multiset.card ν) →₀ ℕ)) :
    Sh hF μ μ' hv he (toUEnd (slRootDatum m₀) K μ ν (KL2.basis (k := K) (C := slCartan m₀) ρ hρ b))
      (conjD (dsign ∘ ιc) * (opΨw (Pcc ιc dsign κ) (ρ b.2.1) * mulMono b.2.2 * opE b.1) *
        conjD (dsign ∘ ιc)) := by
  have hd' : ∀ c, (dsign ∘ ιc) c * (dsign ∘ ιc) c = 1 := fun c => hd _
  rw [KL2.basis_apply, map_mul, map_mul, ← conj_mul_conj hd', ← conj_mul_conj hd']
  refine Sh.mul (Sh.mul (sh_ψw hU dsign κ hχc hιc hd hκ _) (sh_mono hU dsign hχd hd _)) ?_
  rw [conjD_opE _ hd']
  exact sh_toUEnd_e _

end Categorification.Flag.Indep

end
