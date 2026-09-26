/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.SymmetryOmega
import Categorification.Diagrams.KL3.GammaU

/-!
# `ω̃` on `U̇` and the downward halves of KL III §3.5

M. Khovanov, A. Lauda, *A categorification of quantum `sl(n)`*, arXiv:0807.3250v1, §3.4 (the
remark after Definition 3.21: "The 2-functors `ω̃`, `σ̃`, `ψ̃`, `τ̃` on `U` extend to 2-functors on
`U̇`") and §3.5 (TeX label `subsec_dirsumdecs`: (3.54), the display after (3.55), and
Proposition 3.24, label `serre-isoms`).

The symmetry `ω̃ : U → U` (`Categorification.Diagrams.KL3.SymmetryOmega`) inverts orientations,
sends `λ ↦ -λ` and preserves degrees; it therefore extends to the Hom categories of `U̇`
(`omegaGr` on shifted 1-morphisms, `omegaDot` on `U̇ = Kar(Mat(U))`, KL III: "`(E_i 1_λ {t}, e)
↦ (ω̃(E_i 1_λ {t}), ω̃(e))`"). We use it to transport the upward results of §3.5 to downward
strands.

## Downward divided powers

KL III define `E_{-i^{(m)}} 1_λ := (E_{-i^m} 1_λ, e_{-i,m}) {m(1-m)/2 · i·i/2}` with
`e_{-i,m} = (-1)^{m(m-1)/2}` times the downward picture of the nilHecke idempotent `e_{i,m}`.
Since `ω̃` multiplies a diagram by `(-1)` to the number of its crossings of equally labelled
strands, and the idempotent `e_{+i,m} = x^δ ψ_{w_0}` has `m(m-1)/2` such crossings, KL III's
`e_{-i,m}` is `ω̃(e_{+i,m})`. We therefore define (`objFdiv`)
`E_{-i^{(m)}} 1_μ {s} := ω̃(E_{+i^{(m)}} 1_{-μ} {s})`, whose underlying 1-morphism is
`E_{-i^m} 1_μ` and whose idempotent is `ω̃(e_{+i,m})`.

## Main results

* `omegaDot`: `ω̃ : U̇(λ, μ) ⥤ U̇(-λ, -μ)`, additive and `k`-linear; `omegaDotObjOf`,
  `omegaDotNfObj`: on shifted normal-form 1-morphisms `E_w 1_μ {s} ↦ E_{w*} 1_{-μ} {s}` (`w*`:
  the letters dualized, same order); `omegaDotShift`: it commutes with the grading shifts;
* `omegaK0`: the induced `ℤ[q, q⁻¹]`-linear map `K₀(U̇(λ, μ)) → K₀(U̇(-λ, -μ))`, with
  `omegaK0_eC : ω̃[E_w 1_μ] = [E_{w*} 1_{-μ}]`;
* `Fpow_decomp`: **KL III, display after (3.55), second isomorphism**:
  `E_{-i^m} 1_μ ≅ (E_{-i^{(m)}} 1_μ)^{⊕[m]_i!}`;
* `prop324_down`: **KL III Proposition 3.24, second display**: the `ω̃`-image of the first
  display (`prop324`), i.e. `⊕_a E_{…-i^{(2a)} -j -i^{(d+1-2a)}…} 1_λ ≅
  ⊕_a E_{…-i^{(2a+1)} -j -i^{(d-2a)}…} 1_λ` for the downward objects `ω̃(…)`;
* `downSerreK0`: **the downward Serre relation in `K₀`** (`DownSerreK0 RD k`, the hypothesis of
  `gammaQ`), from `serreK0_up` by `ω̃`; hence `gammaQ'`: KL III Proposition 3.27 over `ℚ(q)`
  without hypotheses.
-/

noncomputable section

namespace Categorification.KL3.Diagram

open CategoryTheory CategoryTheory.Limits CategoryTheory.Idempotents StringDiagrams QuantumGroup
  UDot Presentation Categorification.GradedBicat KLR KLR.KLRAlgebra KLR.KL2 LaurentPolynomial

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : RootDatum C X Y) (k : Type w) [CommRing k] [DecidableEq I]

/-! ## `ω̃` on the Hom categories of `U̇` -/

section Dot

variable {RD k}

omit [DecidableEq I] in
/-- `ω̃` on 1-morphisms of `U`: a 1-morphism from `λ` to `μ` goes to one from `λ' = -λ` to
`μ' = -μ`. -/
def omegaHom {lam μ lam' μ' : X} (hl : -lam = lam') (hm : -μ = μ')
    (x : (wtObj RD k lam : U RD k) ⟶ wtObj RD k μ) : (wtObj RD k lam' : U RD k) ⟶ wtObj RD k μ' :=
  ⟨Omega.obj RD x.obj, by
      show -Omega.rX (RD := RD) x.obj.start = lam'
      rw [← hl]; exact congrArg (fun r : X => -r) x.start_eq,
    (Omega.ok_word _ _ x.wf).1, by
      show (psig RD).endR (-Omega.rX (RD := RD) x.obj.start) (Omega.word x.obj.word) = μ'
      rw [(Omega.ok_word _ _ x.wf).2, ← hm]
      exact congrArg (fun r : X => -r) x.endR_eq⟩

omit [DecidableEq I] in
@[simp] theorem omegaHom_obj {lam μ lam' μ' : X} (hl : -lam = lam') (hm : -μ = μ')
    (x : (wtObj RD k lam : U RD k) ⟶ wtObj RD k μ) :
    (omegaHom hl hm x).obj = Omega.obj RD x.obj := rfl

omit [DecidableEq I] in
/-- `ω̃(E_w 1_μ) = E_{w*} 1_{-μ}`. -/
theorem omegaHom_nfHom {lam μ lam' μ' : X} (hl : -lam = lam') (hm : -μ = μ')
    (w : List (Letter I)) (h : wt RD μ w = lam) (h' : wt RD μ' (w.map Letter.dual) = lam') :
    omegaHom hl hm (nfHom RD k lam μ w h) = nfHom RD k lam' μ' (w.map Letter.dual) h' := by
  subst hm
  exact Bicat.Hom.ext (Omega.trO μ w)

variable (lam μ lam' μ' : X) (hl : -lam = lam') (hm : -μ = μ')

/-- `ω̃` on shifted 1-morphisms: `x{t} ↦ ω̃(x){t}` (degrees are preserved, `omegaU_homDeg`). -/
@[simps]
def omegaGr : GrObj (pres RD k) (deg RD) (wtObj RD k lam) (wtObj RD k μ) ⥤
    GrObj (pres RD k) (deg RD) (wtObj RD k lam') (wtObj RD k μ') where
  obj A := ⟨omegaHom hl hm A.x, A.t⟩
  map f := ⟨(omegaU RD k).map f.1, omegaU_homDeg f.2⟩
  map_id _ := Subtype.ext ((omegaU RD k).map_id _)
  map_comp _ _ := Subtype.ext ((omegaU RD k).map_comp _ _)

instance : (omegaGr (RD := RD) (k := k) lam μ lam' μ' hl hm).Additive where
  map_add {_ _ f g} := by
    apply Subtype.ext
    show (omegaU RD k).map (f.1 + g.1) = (omegaU RD k).map f.1 + (omegaU RD k).map g.1
    exact Functor.map_add _

instance : (omegaGr (RD := RD) (k := k) lam μ lam' μ' hl hm).Linear k where
  map_smul {_ _} f r := by
    apply Subtype.ext
    show (omegaU RD k).map (r • f.1) = r • (omegaU RD k).map f.1
    exact Functor.map_smul _ _ _

/-- **`ω̃` on `U̇`** (KL III §3.4: "`(E_i 1_λ {t}, e) ↦ (ω̃(E_i 1_λ {t}), ω̃(e))`"): the functor
`U̇(λ, μ) ⥤ U̇(-λ, -μ)` induced by `ω̃` on formal direct sums and on the Karoubi envelope. -/
abbrev omegaDot : UKar RD k lam μ ⥤ UKar RD k lam' μ' :=
  mapKaroubi (omegaGr (RD := RD) (k := k) lam μ lam' μ' hl hm).mapMat_

variable {lam μ lam' μ' hl hm}

/-- `ω̃(x{t}) = ω̃(x){t}`. -/
theorem omegaDot_objOf (x : (wtObj RD k lam : U RD k) ⟶ wtObj RD k μ) (t : ℤ) :
    (omegaDot lam μ lam' μ' hl hm).obj (objOf x t) = objOf (omegaHom hl hm x) t := by
  fapply Karoubi.ext
  · rfl
  · simp only [eqToHom_refl, Category.comp_id, Category.id_comp]
    exact (omegaGr lam μ lam' μ' hl hm).mapMat_.map_id _

/-- `ω̃(E_w 1_μ {s}) = E_{w*} 1_{-μ} {s}`. -/
theorem omegaDot_nfObj (w : List (Letter I)) (h : wt RD μ w = lam)
    (h' : wt RD μ' (w.map Letter.dual) = lam') (s : ℤ) :
    (omegaDot lam μ lam' μ' hl hm).obj (nfObj RD k lam μ w h s) =
      nfObj RD k lam' μ' (w.map Letter.dual) h' s := by
  rw [nfObj, omegaDot_objOf, omegaHom_nfHom hl hm w h h']

/-- `ω̃((x{t}, e)) = (ω̃(x){t}, ω̃(e))`: on objects given by idempotents, `ω̃` applies `ω̃` to
the underlying 1-morphism and to the idempotent (KL III §3.4). -/
theorem omegaDot_idemObj (x : (wtObj RD k lam : U RD k) ⟶ wtObj RD k μ) (t : ℤ)
    (e : (pres RD k).obj x.obj ⟶ (pres RD k).obj x.obj)
    (he : e ∈ (pres RD k).homDeg (deg RD) x.obj x.obj 0) (hee : e ≫ e = e) :
    (omegaDot lam μ lam' μ' hl hm).obj (idemObj x t e he hee) =
      idemObj (omegaHom hl hm x) t ((omegaU RD k).map e) (omegaU_homDeg he)
        (by rw [← Functor.map_comp, hee]) := by
  fapply Karoubi.ext
  · rfl
  · simp only [eqToHom_refl, Category.comp_id, Category.id_comp]
    rfl

/-- `ω̃` commutes with the grading shifts: `ω̃(A{n}) ≅ ω̃(A){n}`. -/
def omegaDotShift (n : ℤ) (A : UKar RD k lam μ) :
    (omegaDot lam μ lam' μ' hl hm).obj ((shDot (deg RD) n).obj A) ≅
      (shDot (deg RD) n).obj ((omegaDot lam μ lam' μ' hl hm).obj A) :=
  udIso _ _ (Equiv.refl _) (fun _ => rfl) (fun _ => rfl) fun i j => by simp

end Dot

/-! ## `ω̃` on `K₀(U̇)` -/

section K0

variable {RD k} {lam μ lam' μ' : X} (hl : -lam = lam') (hm : -μ = μ')

/-- **`ω̃` on `K₀(U̇(λ, μ))`**: the `ℤ[q, q⁻¹]`-linear map `[A] ↦ [ω̃(A)]` (KL III §3.6: the
2-functors `ω̃`, … induce the corresponding (anti)automorphisms of `K₀(U̇)`). -/
def omegaK0 : K0Kar RD k lam μ →ₗ[LaurentPolynomial ℤ] K0Kar RD k lam' μ' :=
  SplitK0.linearOfShift (SplitK0.map (omegaDot lam μ lam' μ' hl hm)) fun n A => by
    rw [SplitK0.map_of, SplitK0.map_of, SplitK0.shiftHom_of]
    exact SplitK0.of_iso (omegaDotShift n A)

theorem omegaK0_cl (A : UKar RD k lam μ) :
    omegaK0 hl hm (K0U.cl A) = K0U.cl ((omegaDot lam μ lam' μ' hl hm).obj A) := by
  rw [omegaK0, SplitK0.linearOfShift_apply, SplitK0.map_of]

/-- `ω̃[E_w 1_μ] = [E_{w*} 1_{-μ}]`. -/
theorem omegaK0_eC (w : List (Letter I)) (h : wt RD μ w = lam)
    (h' : wt RD μ' (w.map Letter.dual) = lam') :
    omegaK0 hl hm (eC RD k lam μ w h) = eC RD k lam' μ' (w.map Letter.dual) h' := by
  rw [eC, omegaK0_cl, omegaDot_nfObj _ _ h']

end K0

/-! ## The downward Serre relation in `K₀` -/

section Serre

variable {RD k}

omit [DecidableEq I] in
theorem map_dual_serreW (ε : Bool) (i j : I) (N n : ℕ) (a b : List (Letter I)) :
    (a ++ (serreW i j N n).map (fun l => (ε, l)) ++ b).map Letter.dual =
      a.map Letter.dual ++ (serreW i j N n).map (fun l => (!ε, l)) ++ b.map Letter.dual := by
  simp [List.map_append, List.map_map, Function.comp_def]

/-- **The downward Serre relation in `K₀(U̇)`** (the `K₀`-shadow of KL III Proposition 3.24,
second display): obtained from the upward one (`serreK0_up`) by `ω̃`, which exchanges `E_{+i}`
and `E_{-i}`, sends `λ ↦ -λ` and commutes with the grading shifts. -/
theorem downSerreK0 : DownSerreK0 RD k := by
  intro i j hij lam ρ a b hρ
  have hρ' : ∀ n, n ≤ C.dij i j + 1 → wt RD (-lam) (a.map Letter.dual ++
      (serreW i j (C.dij i j + 1) n).map (fun l => (true, l)) ++ b.map Letter.dual) = -ρ := by
    intro n hn
    rw [show (true : Bool) = !false from rfl, ← map_dual_serreW, Omega.wt_map_dual, hρ n hn]
  obtain ⟨Y, hY, hsum⟩ := serreK0_up (RD := RD) (k := k) i j hij (-lam) (-ρ) (a.map Letter.dual)
    (b.map Letter.dual) hρ'
  refine ⟨fun n => omegaK0 (neg_neg ρ) (neg_neg lam) (Y n), fun n hn => ?_, ?_⟩
  · have e := congrArg (omegaK0 (RD := RD) (k := k) (neg_neg ρ) (neg_neg lam)) (hY n hn)
    have hw : (a.map Letter.dual ++ (serreW i j (C.dij i j + 1) n).map (fun l => (true, l)) ++
        b.map Letter.dual).map Letter.dual =
        a ++ (serreW i j (C.dij i j + 1) n).map (fun l => (false, l)) ++ b := by
      simp [List.map_append, List.map_map, Function.comp_def]
    rw [map_smul, omegaK0_eC (neg_neg ρ) (neg_neg lam) _ _ (by rw [hw]; exact hρ n hn)] at e
    rw [← e]
    exact eC_congr hw.symm _ _
  · rw [← map_sum, ← map_sum, hsum]

variable {lam : X} {V : Type*} [AddCommGroup V] [Module (RatFunc ℚ) V] (Φ : QTarget RD k lam V)

/-- **KL III Proposition 3.27 over `ℚ(q)`** (block `U̇ 1_λ`), now unconditional: the assignment
`E_w 1_λ ↦ [E_w 1_λ]` extends to a `ℚ(q)`-linear map `γ : U̇ 1_λ → V` for every
`ℚ(q)`-vector space `V` receiving `K₀(U̇ 1_λ)` compatibly with `q`. -/
def gammaQ' : U1 RD vQ lam →ₗ[RatFunc ℚ] V := gammaQ Φ downSerreK0

/-- `γ(E_w 1_λ) = φ([E_w 1_λ])`. -/
theorem gammaQ'_mk_ew (w : List (Letter I)) :
    gammaQ' Φ (UDot.mk RD vQ lam (ew w)) = Φ.φ (wt RD lam w) (eC RD k _ lam w rfl) :=
  gammaQ_mk_ew Φ downSerreK0 w

end Serre

/-! ## Downward divided powers -/

section Divided

variable (i : I) (m : ℕ) (μ : X)

omit [DecidableEq I] in
theorem wt_neg_ups_replicate :
    -(wν RD (Multiset.replicate m i) + -μ) = wt RD μ (List.replicate m (dn i)) := by
  have h₁ : wt RD (-μ) (ups (List.replicate m i)) = wν RD (Multiset.replicate m i) + -μ := by
    rw [← word_seqPow i m]; exact wt_ups_word (μ := -μ) (seqPow i m)
  have h₂ := Omega.wt_map_dual (RD := RD) (-μ) (ups (List.replicate m i))
  rw [neg_neg] at h₂
  rw [← h₁, ← h₂]
  simp [ups, List.map_replicate]

/-- **KL III (3.54), second line**: the 1-morphism `E_{-i^{(m)}} 1_μ {s}` of `U̇`, defined as
`ω̃(E_{+i^{(m)}} 1_{-μ} {s})`: its underlying 1-morphism is `E_{-i^m} 1_μ {m(1-m)/2 · d_i + s}`
(`omegaDot_idemObj`, `omegaHom_nfHom`) and its idempotent is `ω̃(e_{+i,m})`, which is KL III's
`e_{-i,m} = (-1)^{m(m-1)/2}` (downward picture of `e_{i,m}`): `ω̃` inverts the orientations and
contributes the sign `-1` for each of the `m(m-1)/2` crossings of `ψ_{w_0}`. -/
abbrev objFdiv (s : ℤ) : UKar RD k (wt RD μ (List.replicate m (dn i))) μ :=
  (omegaDot _ (-μ) _ μ (wt_neg_ups_replicate RD i m μ) (neg_neg μ)).obj (objEdiv RD k i m (-μ) s)

/-- **KL III, display after (3.55), second isomorphism**:
`E_{-i^m} 1_μ ≅ (E_{-i^{(m)}} 1_μ)^{⊕[m]_i!}`, a direct sum of `m!` shifted copies of
`E_{-i^{(m)}} 1_μ` with the shifts of the upward decomposition (`Epow_decomp`), the exponents of
`[m]_i!`. -/
theorem Fpow_decomp :
    ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (sh : ι → ℤ),
      Fintype.card ι = m.factorial ∧
      ∑ j, (T (sh j) : LaurentPolynomial ℤ) =
        ∏ n ∈ Finset.range m, ∑ r ∈ Finset.range (n + 1), T (di C i * (2 * (r : ℤ) - n)) ∧
      Nonempty (nfObj RD k (wt RD μ (List.replicate m (dn i))) μ (List.replicate m (dn i)) rfl 0 ≅
        ⨁ fun j => objFdiv RD k i m μ (sh j)) := by
  obtain ⟨ι, hι, hd, sh, hc, hs, ⟨e⟩⟩ := Epow_decomp RD k i m (-μ)
  let F := omegaDot (RD := RD) (k := k) _ (-μ) _ μ (wt_neg_ups_replicate RD i m μ) (neg_neg μ)
  have e₁ : F.obj (nfObj RD k (wν RD (Multiset.replicate m i) + -μ) (-μ) (ups (List.replicate m i))
      (by rw [← word_seqPow i m]; exact wt_ups_word (μ := -μ) (seqPow i m)) 0) ≅
      ⨁ fun j => F.obj (objEdiv RD k i m (-μ) (sh j)) :=
    F.mapIso e ≪≫ F.mapBiproduct _
  have hw : (ups (List.replicate m i)).map Letter.dual = List.replicate m (dn i) := by
    simp [ups, List.map_replicate]
  have e₀ : nfObj RD k (wt RD μ (List.replicate m (dn i))) μ (List.replicate m (dn i)) rfl 0 =
      F.obj (nfObj RD k (wν RD (Multiset.replicate m i) + -μ) (-μ) (ups (List.replicate m i))
        (by rw [← word_seqPow i m]; exact wt_ups_word (μ := -μ) (seqPow i m)) 0) := by
    rw [omegaDot_nfObj _ _ (by rw [hw])]
    exact nfObj_congr_list RD k hw.symm _ _ 0
  exact ⟨ι, hι, hd, sh, hc, hs, ⟨eqToIso e₀ ≪≫ e₁⟩⟩

end Divided

/-! ## KL III Proposition 3.24, second display -/

section Serre324

variable {ν : Multiset I} {t : Seq ν} {p N : ℕ} {bs : List (ℕ × ℕ)} {i j : I}
  (hpN : p + N < Multiset.card ν)
  (ht₀ : ∀ r : Fin (Multiset.card ν), (r : ℕ) = p → t.lbl r = j)
  (ht : ∀ r : Fin (Multiset.card ν), p < r → (r : ℕ) ≤ p + N → t.lbl r = i)
  (hb : IsBlocks t bs) (hbs : ∀ b ∈ bs, b.1 + b.2 ≤ p ∨ p + N + 1 ≤ b.1) (hij : i ≠ j)

omit [DecidableEq I] in
theorem neg_wν_add (ν : Multiset I) (μ : X) : -(wν RD ν + -μ) = -wν RD ν + μ := by abel

/-- **KL III Proposition 3.24, second display** (downward strands): for `i ≠ j`,
`d = d_ij = -⟨i, j_X⟩`, `N = d + 1`,
`⊕_{n ≤ N even} ω̃(E_{…i^{(n)} j i^{(N-n)}…} 1_{-μ}) ≅ ⊕_{n ≤ N odd} ω̃(E_{…i^{(n)} j i^{(N-n)}…} 1_{-μ})`,
i.e. `⊕_a E_{…-i^{(2a)} -j -i^{(d+1-2a)}…} 1_μ ≅ ⊕_a E_{…-i^{(2a+1)} -j -i^{(d-2a)}…} 1_μ`: the
image under `ω̃` of the first display (`prop324`). The downward objects `ω̃(E_{…} 1_{-μ})` are
`(E_{…}^* 1_μ, ω̃(e))` (`omegaDot_idemObj`): the dual (downward) sequences with the idempotent
`ω̃(ϕ_{ν,-μ}(1_{…i^{(n)} j i^{(N-n)}…}))`, which on divided-power blocks is KL III's `e_{-i,a}`
(see `objFdiv`); KL III's proof ("via homomorphisms `ϕ_{-ν,λ}`") uses `ϕ_{-ν,λ} = ω̃ ∘ ϕ_{ν,-λ}`
in this form. -/
def prop324_down (hN : N = C.dij i j + 1) (μ : X) (c : ℤ) :
    (⨁ fun n : {n // n ∈ serreEvens N} =>
        (omegaDot _ (-μ) _ μ (neg_wν_add RD ν μ) (neg_neg μ)).obj
          (kobj RD (-μ) (serreCorner C k hpN ht₀ ht hb hbs hij n.1 (mem_serreEvens.1 n.2).1)
            (c - (((n.1.choose 2 : ℕ) : ℤ) + (((N - n.1).choose 2 : ℕ) : ℤ)) * di C i))) ≅
      ⨁ fun n : {n // n ∈ serreOdds N} =>
        (omegaDot _ (-μ) _ μ (neg_wν_add RD ν μ) (neg_neg μ)).obj
          (kobj RD (-μ) (serreCorner C k hpN ht₀ ht hb hbs hij n.1 (mem_serreOdds.1 n.2).1)
            (c - (((n.1.choose 2 : ℕ) : ℤ) + (((N - n.1).choose 2 : ℕ) : ℤ)) * di C i)) :=
  let F := omegaDot (RD := RD) (k := k) _ (-μ) _ μ (neg_wν_add RD ν μ) (neg_neg μ)
  (F.mapBiproduct (fun n : {n // n ∈ serreEvens N} =>
      kobj RD (-μ) (serreCorner C k hpN ht₀ ht hb hbs hij n.1 (mem_serreEvens.1 n.2).1)
        (c - (((n.1.choose 2 : ℕ) : ℤ) + (((N - n.1).choose 2 : ℕ) : ℤ)) * di C i))).symm ≪≫
    F.mapIso (prop324 RD k hpN ht₀ ht hb hbs hij hN (-μ) c) ≪≫
    F.mapBiproduct (fun n : {n // n ∈ serreOdds N} =>
      kobj RD (-μ) (serreCorner C k hpN ht₀ ht hb hbs hij n.1 (mem_serreOdds.1 n.2).1)
        (c - (((n.1.choose 2 : ℕ) : ℤ) + (((N - n.1).choose 2 : ℕ) : ℤ)) * di C i))

end Serre324

end Categorification.KL3.Diagram
