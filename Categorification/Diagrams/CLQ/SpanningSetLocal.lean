/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.CLQ.SortDecomp
import Categorification.Diagrams.CLQ.MixedR3Sl2
import Categorification.Diagrams.CLQ.SymmetryOmega
import Categorification.Diagrams.CLQ.Spanning
import Categorification.Diagrams.KL3.SpanningSetLocal
import Categorification.Diagrams.CLQ.EndOne

/-!
# Local relations of `U_Q(g)` modulo diagrams with fewer crossings

M. Khovanov, A. Lauda, *A categorification of quantum `sl(n)`*, arXiv:0807.3250v1, §3.2.3, proof
of Proposition 3.11 (homotopies of dotted diagrams hold modulo diagrams with fewer crossings),
for the 2-category `U_Q(g)` of S. Cautis, A. D. Lauda, arXiv:1111.1431v3, Definition 1.1, with
`r = 1` (`CLQ.pres`). This is the version of `Categorification.Diagrams.KL3.SpanningSetLocal`
for general scalars; it is input for Webster, arXiv:1309.3796v3, Lemma 4.29 at general `Q`.

`LeL c` is the span of the diagrams with at most `c` crossing layers (`ccnt`), and
`xLay l₁ l₂` is the crossing of two strands with signed labels (an upward, downward or sideways
crossing).

## Differences from KL III

* The inversion of orientations maps `U_Q(g)` to `U_{Q^θ}(g)` (`omegaHom`, from
  `CLQ.lin_omegaSLin_eq_zero`); relations for downward strands are transported from
  `U_{Q^θ}(g)` (`omega_transport`), which needs `r = 1` so that `Q^{θθ} = Q`. The statements
  proved this way carry the hypothesis `hr : ∀ i, sc.r i = 1`.
* The rotation of a downward crossing is a sideways crossing up to the unit `t_{ij}^{-1}`
  (`dg_wls_crosslL`, `dg_wls_crossrL`). In Reidemeister 3 both sides contain the same two
  sideways crossings, so the units cancel and `r3` holds with coefficient `1`; the pitchfork
  moves `capPF`, `cupPF` hold up to a unit.

## Main results

* `isBub_mem_leL`: every element of the image of `Π_λ` (real and fake bubbles and their
  products) is a linear combination of crossingless closed diagrams.
* `ds0`, `ds1`: dots slide through crossings modulo diagrams without crossings.
* `r2`, `r3`: Reidemeister 2 and 3 for all orientations, modulo lower terms.
* `cupCurl`, `capCurl`: curls on cups and caps are lower terms.
* `capPF`, `cupPF`: pitchforks, up to a unit, modulo lower terms.
-/

-- Preserve elaboration of semireducible diagram transports.
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.KL3.Diagram.CLQ

open CategoryTheory StringDiagrams QuantumGroup UDot Presentation

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  {RD : WeightDatum C X Y} {k : Type w} [CommRing k] {sc : CL.CLScalars C k}

/-! ## Crossing counts and lower terms -/

variable (RD k sc) in
/-- Linear combinations of diagrams `E_s 1_ν ⟶ E_t 1_ν` with at most `c` crossings. -/
def LeL (ν : X) (s t : List (Letter I)) (c : ℕ) :
    Submodule k ((pres RD k sc).obj (ob RD ν s) ⟶ (pres RD k sc).obj (ob RD ν t)) :=
  Submodule.span k {f | ∃ L, ccnt L ≤ c ∧ f = NF.dg (pres RD k sc) ν s t L}

theorem dg_mem_leL {ν : X} {s t : List (Letter I)} {c : ℕ} {L : List (LayerData I)}
    (h : ccnt L ≤ c) : NF.dg (pres RD k sc) ν s t L ∈ LeL RD k sc ν s t c :=
  Submodule.subset_span ⟨L, h, rfl⟩

theorem leL_mono {ν : X} {s t : List (Letter I)} {c c' : ℕ} (h : c ≤ c') :
    LeL RD k sc ν s t c ≤ LeL RD k sc ν s t c' :=
  Submodule.span_mono fun _ ⟨L, hL, e⟩ => ⟨L, hL.trans h, e⟩

theorem dg_comp_dg_mem_leL {ν : X} {s t r : List (Letter I)} {c : ℕ} {L M : List (LayerData I)}
    (h : ccnt L + ccnt M ≤ c) : NF.dg (pres RD k sc) ν s t L ≫ NF.dg (pres RD k sc) ν t r M ∈ LeL RD k sc ν s r c := by
  by_cases hA : SChain s L t
  · by_cases hB : SChain t M r
    · rw [NF.dg_comp hA hB]; exact dg_mem_leL (by rw [ccnt_append]; omega)
    · rw [NF.dg_of_not hB, Limits.comp_zero]; exact Submodule.zero_mem _
  · rw [NF.dg_of_not hA, Limits.zero_comp]; exact Submodule.zero_mem _

/-- Composition adds crossings. -/
theorem leL_comp {ν : X} {s t r : List (Letter I)} {c c' : ℕ} {f g}
    (hf : f ∈ LeL RD k sc ν s t c) (hg : g ∈ LeL RD k sc ν t r c') :
    f ≫ g ∈ LeL RD k sc ν s r (c + c') := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨L, hL, rfl⟩ := hf
    induction hg using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨M, hM, rfl⟩ := hg
      exact dg_comp_dg_mem_leL (by omega)
    | zero => rw [Limits.comp_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [Preadditive.comp_add]; exact Submodule.add_mem _ hx hy
    | smul r x _ hx => rw [Linear.comp_smul]; exact Submodule.smul_mem _ r hx
  | zero => rw [Limits.zero_comp]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [Preadditive.add_comp]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [Linear.smul_comp]; exact Submodule.smul_mem _ r hx

theorem dg_comp_leL {ν : X} {s t r : List (Letter I)} {c : ℕ} {g} (M : List (LayerData I))
    (hg : g ∈ LeL RD k sc ν t r c) : NF.dg (pres RD k sc) ν s t M ≫ g ∈ LeL RD k sc ν s r (ccnt M + c) :=
  leL_comp (dg_mem_leL le_rfl) hg

theorem leL_comp_dg {ν : X} {s t r : List (Letter I)} {c : ℕ} {f}
    (hf : f ∈ LeL RD k sc ν s t c) (M : List (LayerData I)) :
    f ≫ NF.dg (pres RD k sc) ν t r M ∈ LeL RD k sc ν s r (c + ccnt M) :=
  leL_comp hf (dg_mem_leL le_rfl)

/-- Placement between strands preserves crossing counts. -/
theorem plcL_leL {μ : X} {u v s t : List (Letter I)} {c : ℕ} {f}
    (hf : f ∈ LeL RD k sc (wt RD μ v) s t c) :
    NF.plcL (pres RD k sc) μ u v s t f ∈ LeL RD k sc μ (u ++ s ++ v) (u ++ t ++ v) c := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨L, hL, rfl⟩ := hf
    rw [NF.plcL_dg]; exact dg_mem_leL (by rw [ccnt_map_whL]; exact hL)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [map_smul]; exact Submodule.smul_mem _ r hx

theorem ctxL_leL {μ : X} {s₀ t₀ : List (Letter I)} {pre post : List (LayerData I)}
    {u v s t : List (Letter I)} {c : ℕ} {f} (hf : f ∈ LeL RD k sc (wt RD μ v) s t c) :
    NF.ctxL (pres RD k sc) μ s₀ t₀ pre u v post s t f ∈ LeL RD k sc μ s₀ t₀ (ccnt pre + c + ccnt post) := by
  have h := dg_comp_leL (s := s₀) pre (leL_comp_dg (plcL_leL (u := u) hf) (r := t₀) post)
  rw [← add_assoc] at h
  exact h

/-! ## Bubbles are linear combinations of crossingless closed diagrams -/

theorem bubMap_mem_leL (lam : X) (p : PiLam I k) :
    (bubMap RD k sc lam p).val ∈ LeL RD k sc lam [] [] 0 := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    rw [MvPolynomial.algHom_C, EndOne.val_algebraMap, ← NF.dg_nil (P := pres RD k sc) lam []]
    exact Submodule.smul_mem _ _ (dg_mem_leL le_rfl)
  | add p q hp hq => rw [map_add]; exact Submodule.add_mem _ hp hq
  | mul_X p s hp =>
    rw [map_mul, EndOne.val_mul]
    have hX : (bubMap RD k sc lam (MvPolynomial.X s)).val = bubGen RD k sc lam s.1 (s.2 + 1) := by
      simp only [bubMap, MvPolynomial.aeval_X]; rfl
    rw [hX]
    have key : bubGen RD k sc lam s.1 (s.2 + 1) ∈ LeL RD k sc lam [] [] 0 := ?_
    · have := leL_comp key hp
      simpa using this
    unfold bubGen
    have e : ∀ m : ℤ, 0 ≤ m → ∀ f : ℤ → End ((pres RD k sc).obj (ob RD lam [])),
        (∀ n : ℕ, f n ∈ LeL RD k sc lam [] [] 0) → f m ∈ LeL RD k sc lam [] [] 0 := by
      intro m hm f hf
      obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hm
      exact hf n
    split_ifs
    · refine e _ (by omega) (NF.cwU (pres RD k sc) lam s.1) fun n => ?_
      rw [NF.cwU_of_nonneg]
      exact dg_mem_leL (by simp [cwLs, ccnt_cons, ccnt_append, ccnt_replicate_dot, Shape.isCross])
    · refine e _ (by omega) (NF.ccwU (pres RD k sc) lam s.1) fun n => ?_
      rw [NF.ccwU_of_nonneg]
      exact dg_mem_leL (by simp [ccwLs, ccnt_cons, ccnt_append, ccnt_replicate_dot, Shape.isCross])

/-- **Bubbles are crossingless**: every element of the image of `Π_λ` is a linear combination of
closed diagrams without crossings. -/
theorem isBub_mem_leL {lam : X} {β : End ((pres RD k sc).obj (ob RD lam []))}
    (hβ : IsBub RD k sc lam β) : β ∈ LeL RD k sc lam [] [] 0 := by
  obtain ⟨p, hp⟩ := hβ
  have : β = (bubMap RD k sc lam p).val := by
    have := congrArg EndOne.val hp
    exact this.symm
  rw [this]; exact bubMap_mem_leL lam p

/-! ## Rewriting modulo lower terms -/

theorem leL_sub_trans {ν : X} {s t : List (Letter I)} {c : ℕ} {a b d}
    (h₁ : a - b ∈ LeL RD k sc ν s t c) (h₂ : b - d ∈ LeL RD k sc ν s t c) :
    a - d ∈ LeL RD k sc ν s t c := by
  have := Submodule.add_mem _ h₁ h₂; rwa [sub_add_sub_cancel] at this

theorem leL_sub_of_eq {ν : X} {s t : List (Letter I)} {c : ℕ} {a b} (h : a = b) :
    a - b ∈ LeL RD k sc ν s t c := by
  rw [h, sub_self]; exact Submodule.zero_mem _

/-- **A local relation modulo lower terms, in context.** -/
theorem dg_mod_ctx (μ : X) {s₀ t₀ : List (Letter I)} (pre post : List (LayerData I))
    (u v : List (Letter I)) {s t : List (Letter I)} {A B : List (LayerData I)} {c : ℕ}
    (E : NF.dg (pres RD k sc) (wt RD μ v) s t A - NF.dg (pres RD k sc) (wt RD μ v) s t B ∈ LeL RD k sc (wt RD μ v) s t c)
    (hpre : SChain s₀ pre (u ++ s ++ v)) (hpost : SChain (u ++ t ++ v) post t₀) :
    NF.dg (pres RD k sc) μ s₀ t₀ (pre ++ A.map (whL u v) ++ post) -
        NF.dg (pres RD k sc) μ s₀ t₀ (pre ++ B.map (whL u v) ++ post) ∈
      LeL RD k sc μ s₀ t₀ (ccnt pre + c + ccnt post) := by
  rw [← NF.ctxL_dg (pres RD k sc) μ hpre hpost A, ← NF.ctxL_dg (pres RD k sc) μ hpre hpost B, ← map_sub]
  exact ctxL_leL E

/-- **A local relation modulo lower terms, at a position.** -/
theorem dg_mod_at {μ : X} {s₀ t₀ : List (Letter I)} (L : List (LayerData I)) (n : ℕ)
    (u v : List (Letter I)) {s t : List (Letter I)} {A B : List (LayerData I)} {c : ℕ}
    (E : NF.dg (pres RD k sc) (wt RD μ v) s t A - NF.dg (pres RD k sc) (wt RD μ v) s t B ∈ LeL RD k sc (wt RD μ v) s t c)
    (hpre : SChain s₀ (L.take n) (u ++ s ++ v))
    (hpost : SChain (u ++ t ++ v) (L.drop (n + A.length)) t₀)
    (hL : (L.drop n).take A.length = A.map (whL u v)) :
    NF.dg (pres RD k sc) μ s₀ t₀ L - NF.dg (pres RD k sc) μ s₀ t₀ (L.take n ++ B.map (whL u v) ++ L.drop (n + A.length)) ∈
      LeL RD k sc μ s₀ t₀ (ccnt (L.take n) + c + ccnt (L.drop (n + A.length))) := by
  have e : L = L.take n ++ A.map (whL u v) ++ L.drop (n + A.length) := by
    rw [← hL]; exact list_split_at' L n A.length
  have h := dg_mod_ctx μ (L.take n) (L.drop (n + A.length)) u v E hpre hpost
  rw [← e] at h
  exact h

/-- **A local diagram in the lower span, in context.** -/
theorem dg_mem_ctx (μ : X) {s₀ t₀ : List (Letter I)} (pre post : List (LayerData I))
    (u v : List (Letter I)) {s t : List (Letter I)} {A : List (LayerData I)} {c : ℕ}
    (E : NF.dg (pres RD k sc) (wt RD μ v) s t A ∈ LeL RD k sc (wt RD μ v) s t c)
    (hpre : SChain s₀ pre (u ++ s ++ v)) (hpost : SChain (u ++ t ++ v) post t₀) :
    NF.dg (pres RD k sc) μ s₀ t₀ (pre ++ A.map (whL u v) ++ post) ∈
      LeL RD k sc μ s₀ t₀ (ccnt pre + c + ccnt post) := by
  rw [← NF.ctxL_dg (pres RD k sc) μ hpre hpost A]
  exact ctxL_leL E

/-! ## The crossing of two strands -/

theorem leL_sub_trans_le {ν : X} {s t : List (Letter I)} {c₁ c : ℕ} {a b d}
    (h₁ : a - b ∈ LeL RD k sc ν s t c₁) (hc : c₁ ≤ c) (h₂ : b - d ∈ LeL RD k sc ν s t c) :
    a - d ∈ LeL RD k sc ν s t c :=
  leL_sub_trans (leL_mono hc h₁) h₂

theorem leL_sub_self {ν : X} {s t : List (Letter I)} {c : ℕ} (a) :
    a - a ∈ LeL RD k sc ν s t c := by rw [sub_self]; exact Submodule.zero_mem _

/-- `mswapQ n`: the interchange law at the layers `n`, `n + 1` of the first diagram of a goal
`dg μ s t L - b ∈ S`. -/
macro "mswapQ " n:term:max : tactic => `(tactic| (
  first
    | refine sub_mem_of_eq_left (NF.dg_swapLR_at _ $n _ _ _ (by exact rfl) (by exact rfl)
        (by exact rfl)) ?_
    | refine sub_mem_of_eq_left (NF.dg_swapRL_at _ $n _ _ _ (by exact rfl) (by exact rfl)
        (by exact rfl)) ?_
  try dnorm))

/-- `matQ n u v E`: an exact local rewrite in the first diagram of a goal `dg μ s t L - b ∈ S`. -/
macro "matQ " n:term:max u:term:max v:term:max E:term:max : tactic => `(tactic| (
  refine sub_mem_of_eq_left (NF.dg_step_at _ $n $u $v $E (by (try dnorm); schain)
    (by (try dnorm); schain) (by dnorm)) ?_
  try dnorm))

/-- `iswapQ n`: the interchange law at the layers `n`, `n + 1` of the diagram of a goal
`dg μ s t L ∈ S`. -/
macro "iswapQ " n:term:max : tactic => `(tactic| (
  first
    | refine mem_of_eq_left (NF.dg_swapLR_at _ $n _ _ _ (by exact rfl) (by exact rfl)
        (by exact rfl)) ?_
    | refine mem_of_eq_left (NF.dg_swapRL_at _ $n _ _ _ (by exact rfl) (by exact rfl)
        (by exact rfl)) ?_
  try dnorm))

/-- `iatQ n u v E`: an exact local rewrite in the diagram of a goal `dg μ s t L ∈ S`. -/
macro "iatQ " n:term:max u:term:max v:term:max E:term:max : tactic => `(tactic| (
  refine mem_of_eq_left (NF.dg_step_at _ $n $u $v $E (by (try dnorm); schain)
    (by (try dnorm); schain) (by dnorm)) ?_
  try dnorm))

/-- Normalizes lists of layers, unfolding the crossings `xLay`. -/
macro "xnormQ" : tactic => `(tactic| (
  try simp only [xLay_up_up, xLay_dn_dn, xLay_up_dn, xLay_dn_up, crosslL, crossrL]
  try dnorm))

/-- `mmodQ n u v E`: a local rewrite modulo lower terms in the first diagram of a goal
`dg μ s t L - b ∈ LeL μ s t c`. -/
macro "mmodQ " n:term:max u:term:max v:term:max E:term:max : tactic => `(tactic| (
  refine leL_sub_trans_le (dg_mod_at _ $n $u $v $E (by xnormQ; schain) (by xnormQ; schain)
    (by xnormQ)) (by xnormQ; simp [ccnt_cons, ccnt_append, Shape.isCross]) ?_
  try xnormQ))

/-! ## Dots slide through upward crossings -/

/-- A dot on the left upper strand of the upward crossing `ψ_{ij}` slides to the right lower
strand, modulo a diagram without crossings. -/
theorem dsUp0 (ν : X) (i j : I) :
    NF.dg (pres RD k sc) ν [up i, up j] [up j, up i] (xLay (up i) (up j) ++ [([], .dot (up j), [up i])]) -
      NF.dg (pres RD k sc) ν [up i, up j] [up j, up i] ([([up i], .dot (up j), [])] ++ xLay (up i) (up j)) ∈
        LeL RD k sc ν [up i, up j] [up j, up i] 0 := by
  simp only [xLay, List.cons_append, List.nil_append]
  by_cases h : i = j
  · subst h
    rw [dg_slideLEq, add_sub_cancel_left]; exact dg_mem_leL le_rfl
  · exact leL_sub_of_eq (dg_slideLNe RD k sc ν i j h)

/-- A dot on the right upper strand of `ψ_{ij}` slides to the left lower strand. -/
theorem dsUp1 (ν : X) (i j : I) :
    NF.dg (pres RD k sc) ν [up i, up j] [up j, up i] (xLay (up i) (up j) ++ [([up j], .dot (up i), [])]) -
      NF.dg (pres RD k sc) ν [up i, up j] [up j, up i] ([([], .dot (up i), [up j])] ++ xLay (up i) (up j)) ∈
        LeL RD k sc ν [up i, up j] [up j, up i] 0 := by
  simp only [xLay, List.cons_append, List.nil_append]
  by_cases h : i = j
  · subst h
    rw [dg_slideREq, sub_add_cancel_left, ← neg_one_smul k]
    exact Submodule.smul_mem _ _ (dg_mem_leL le_rfl)
  · exact leL_sub_of_eq (dg_slideRNe RD k sc ν i j h).symm

/-! ## Transport by the orientation reversal `ω̃`

In `U_Q(g)` the inversion of orientations `ω̃` maps `U_Q(g)` to `U_{Q^θ}(g)` (`thetaScalars`,
`Categorification.Diagrams.CLQ.SymmetryOmega`). On 2-morphisms it is the `k`-linear map
`omegaHom`, obtained from `omegaSLin` on linear combinations of diagrams, which descends to
`U_Q(g)` by `lin_omegaSLin_eq_zero`. A relation modulo lower terms in `U_Q(g)` is transported to
`U_{Q^θ}(g)` (`omega_transport_theta`); for scalars with `r = 1`, `Q^{θθ} = Q`, so a relation in
`U_{Q^θ}(g)` gives the orientation-reversed relation in `U_Q(g)` (`omega_transport`). -/

section Omega

variable [DecidableEq I]

omit [DecidableEq I] in
omit [DecidableEq I] in
variable (RD k sc) in
/-- The class map `LinDiagram k a b → Hom(a, b)` of `U_Q(g)`, as a `k`-linear map. -/
def linMap (a b : Obj (psig RD)) :
    LinDiagram k a b →ₗ[k] ((pres RD k sc).obj a ⟶ (pres RD k sc).obj b) where
  toFun := (pres RD k sc).lin
  map_add' := Presentation.lin_add _
  map_smul' := Presentation.lin_smul _

variable (sc) in
/-- **The inversion of orientations `ω̃ : U_Q(g) → U_{Q^θ}(g)` on 2-morphisms** with well-formed
source, with the sign of KL III's `ω̃`. -/
def omegaHom {a b : Obj (psig RD)} (ha : a.WF) :
    ((pres RD k sc).obj a ⟶ (pres RD k sc).obj b) →ₗ[k]
      ((pres RD k (CLQ.thetaScalars RD sc)).obj (Omega.obj RD a) ⟶
        (pres RD k (CLQ.thetaScalars RD sc)).obj (Omega.obj RD b)) :=
  ((LinearMap.ker (linMap RD k sc a b)).liftQ
      ((linMap RD k (CLQ.thetaScalars RD sc) _ _).comp (CLQ.omegaSLin k))
      (fun F hF => CLQ.lin_omegaSLin_eq_zero sc F ha hF)).comp
    ((linMap RD k sc a b).quotKerEquivOfSurjective
      (fun f => (pres RD k sc).lin_surjective f)).symm.toLinearMap

theorem omegaHom_lin {a b : Obj (psig RD)} (ha : a.WF) (F : LinDiagram k a b) :
    omegaHom sc ha ((pres RD k sc).lin F) =
      (pres RD k (CLQ.thetaScalars RD sc)).lin (CLQ.omegaSLin k F) := by
  change omegaHom sc ha (linMap RD k sc a b F) = _
  simp only [omegaHom, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    LinearMap.quotKerEquivOfSurjective_symm_apply, Submodule.liftQ_apply]
  rfl

/-- `ω̃` on a normal-form diagram: reverse the orientations of the layers (`Omega.wls`), dualize
the boundary letters, send `ν ↦ -ν`, and multiply by `(-1)` to the number of crossings of
equally labelled strands. -/
theorem omegaHom_dg (ν : X) {s t : List (Letter I)} (L : List (LayerData I)) (h : SChain s L t) :
    omegaHom sc (ob_wf RD ν s) (NF.dg (pres RD k sc) ν s t L) =
      ((Sig.sgnS L : ℤ) : k) • TRQ RD k (CLQ.thetaScalars RD sc) (Omega.trO ν s) (Omega.trO ν t)
        (NF.dg (pres RD k (CLQ.thetaScalars RD sc)) (-ν) (s.map Letter.dual) (t.map Letter.dual)
          (Omega.wls L)) := by
  rw [NF.dg_of h, show (pres RD k sc).diag (mkD RD ν L h) =
    (pres RD k sc).lin (LinDiagram.of (mkD RD ν L h)) from rfl, omegaHom_lin,
    show (LinDiagram.of (mkD RD ν L h) : LinDiagram k _ _) = Finsupp.single (mkD RD ν L h) 1
      from rfl, CLQ.omegaSLin_single, one_mul, Presentation.lin_smul, Presentation.lin_of,
    layers_mkD, Sig.sgn_layList, NF.dg_of (Omega.sChain_wls h), TRQ_diag]
  congr 1
  apply (pres RD k (CLQ.thetaScalars RD sc)).diag_eq_of_layers_eq
  rw [Diagram.layers_cast]
  exact Omega.layers_reflD_mkD (RD := RD) ν L h

theorem omega_leL {ν : X} {s t : List (Letter I)} {c : ℕ} {f}
    (hf : f ∈ LeL RD k sc ν s t c) :
    omegaHom sc (ob_wf RD ν s) f ∈
      (LeL RD k (CLQ.thetaScalars RD sc) (-ν) (s.map Letter.dual) (t.map Letter.dual) c).map
        (TRQ RD k (CLQ.thetaScalars RD sc) (Omega.trO ν s) (Omega.trO ν t)) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨L, hL, rfl⟩ := hf
    by_cases h : SChain s L t
    · rw [omegaHom_dg ν L h, ← map_smul]
      exact Submodule.mem_map_of_mem (Submodule.smul_mem _ _ (dg_mem_leL (by rwa [ccnt_wls])))
    · rw [NF.dg_of_not h, map_zero]; exact Submodule.zero_mem _
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [map_smul]; exact Submodule.smul_mem _ r hx

omit [DecidableEq I] in
theorem TRQ_mem_map_iff {a a' b b' : Obj (psig RD)} (ea : a = a') (eb : b = b')
    {S : Submodule k ((pres RD k sc).obj a' ⟶ (pres RD k sc).obj b')} {f} :
    TRQ RD k sc ea eb f ∈ S.map (TRQ RD k sc ea eb) ↔ f ∈ S := by
  refine ⟨fun ⟨g, hg, e⟩ => ?_, fun h => Submodule.mem_map_of_mem h⟩
  have : g - f = 0 := by
    rw [← TRQ_eq_zero ea eb, map_sub, e, sub_self]
  rwa [sub_eq_zero.1 this] at hg

/-- **Transport of a relation modulo lower terms by `ω̃ : U_Q(g) → U_{Q^θ}(g)`**: if two diagrams
with the same sign agree in `U_Q(g)` modulo diagrams with at most `c` crossings, their
orientation reversals agree in `U_{Q^θ}(g)` modulo diagrams with at most `c` crossings. -/
theorem omega_transport_theta {ν : X} {s t : List (Letter I)} {c : ℕ}
    {L₁ L₂ : List (LayerData I)} (h₁ : SChain s L₁ t) (h₂ : SChain s L₂ t)
    (hs : Sig.sgnS L₁ = Sig.sgnS L₂)
    (h : NF.dg (pres RD k sc) ν s t L₁ - NF.dg (pres RD k sc) ν s t L₂ ∈ LeL RD k sc ν s t c) :
    NF.dg (pres RD k (CLQ.thetaScalars RD sc)) (-ν) (s.map Letter.dual) (t.map Letter.dual)
        (Omega.wls L₁) -
      NF.dg (pres RD k (CLQ.thetaScalars RD sc)) (-ν) (s.map Letter.dual) (t.map Letter.dual)
        (Omega.wls L₂) ∈
      LeL RD k (CLQ.thetaScalars RD sc) (-ν) (s.map Letter.dual) (t.map Letter.dual) c := by
  have h' := omega_leL h
  rw [map_sub, omegaHom_dg ν L₁ h₁, omegaHom_dg ν L₂ h₂, hs, ← smul_sub,
    ← LinearMap.map_sub (TRQ RD k _ _ _)] at h'
  have := Submodule.smul_mem _ ((Sig.sgnS L₂ : ℤ) : k) h'
  rwa [smul_smul, ← Int.cast_mul, sgnS_sq, Int.cast_one, one_smul, TRQ_mem_map_iff] at this

theorem omega_transport_single_theta {ν : X} {s t : List (Letter I)} {c : ℕ}
    {L : List (LayerData I)} (hL : SChain s L t)
    (h : NF.dg (pres RD k sc) ν s t L ∈ LeL RD k sc ν s t c) :
    NF.dg (pres RD k (CLQ.thetaScalars RD sc)) (-ν) (s.map Letter.dual) (t.map Letter.dual)
        (Omega.wls L) ∈
      LeL RD k (CLQ.thetaScalars RD sc) (-ν) (s.map Letter.dual) (t.map Letter.dual) c := by
  have h' := omega_leL h
  rw [omegaHom_dg ν L hL] at h'
  have := Submodule.smul_mem _ ((Sig.sgnS L : ℤ) : k) h'
  rwa [smul_smul, ← Int.cast_mul, sgnS_sq, Int.cast_one, one_smul, TRQ_mem_map_iff] at this

/-- **Transport of a relation modulo lower terms by `ω̃`, into `U_Q(g)`** (`r = 1`, so
`Q^{θθ} = Q`): a relation modulo lower terms in `U_{Q^θ}(g)` gives the orientation-reversed
relation in `U_Q(g)`. -/
theorem omega_transport (hr : ∀ i, sc.r i = 1) {ν : X} {s t : List (Letter I)} {c : ℕ}
    {L₁ L₂ : List (LayerData I)} (h₁ : SChain s L₁ t) (h₂ : SChain s L₂ t)
    (hs : Sig.sgnS L₁ = Sig.sgnS L₂)
    (h : NF.dg (pres RD k (CLQ.thetaScalars RD sc)) ν s t L₁ -
      NF.dg (pres RD k (CLQ.thetaScalars RD sc)) ν s t L₂ ∈
        LeL RD k (CLQ.thetaScalars RD sc) ν s t c) :
    NF.dg (pres RD k sc) (-ν) (s.map Letter.dual) (t.map Letter.dual) (Omega.wls L₁) -
      NF.dg (pres RD k sc) (-ν) (s.map Letter.dual) (t.map Letter.dual) (Omega.wls L₂) ∈
      LeL RD k sc (-ν) (s.map Letter.dual) (t.map Letter.dual) c := by
  have h' := omega_transport_theta h₁ h₂ hs h
  rwa [CLQ.thetaScalars_thetaScalars sc hr] at h'

theorem omega_transport_single (hr : ∀ i, sc.r i = 1) {ν : X} {s t : List (Letter I)} {c : ℕ}
    {L : List (LayerData I)} (hL : SChain s L t)
    (h : NF.dg (pres RD k (CLQ.thetaScalars RD sc)) ν s t L ∈
      LeL RD k (CLQ.thetaScalars RD sc) ν s t c) :
    NF.dg (pres RD k sc) (-ν) (s.map Letter.dual) (t.map Letter.dual) (Omega.wls L) ∈
      LeL RD k sc (-ν) (s.map Letter.dual) (t.map Letter.dual) c := by
  have h' := omega_transport_single_theta hL h
  rwa [CLQ.thetaScalars_thetaScalars sc hr] at h'

end Omega

/-! ## Dots slide through all crossings -/

theorem leL_sub_comm {ν : X} {s t : List (Letter I)} {c : ℕ} {a b}
    (h : a - b ∈ LeL RD k sc ν s t c) : b - a ∈ LeL RD k sc ν s t c := by
  rw [← neg_sub]; exact Submodule.neg_mem _ h

theorem dsUpDn0 (ν : X) (i j : I) :
    NF.dg (pres RD k sc) ν [up i, dn j] [dn j, up i] (xLay (up i) (dn j) ++ [([], .dot (dn j), [up i])]) -
      NF.dg (pres RD k sc) ν [up i, dn j] [dn j, up i] ([([up i], .dot (dn j), [])] ++ xLay (up i) (dn j)) ∈
        LeL RD k sc ν [up i, dn j] [dn j, up i] 0 := by
  xnormQ
  mswapQ 2; mswapQ 1
  matQ 0 [] [up i, dn j] (dg_dot_cupDn RD k sc j _).symm
  mmodQ 1 [dn j] [dn j] (leL_sub_comm (dsUp1 _ j i))
  matQ 2 [dn j, up i] [] (dg_dot_cap_dn RD k sc _ j).symm
  mswapQ 1; mswapQ 0
  exact leL_sub_self _

theorem dsUpDn1 (ν : X) (i j : I) :
    NF.dg (pres RD k sc) ν [up i, dn j] [dn j, up i] (xLay (up i) (dn j) ++ [([dn j], .dot (up i), [])]) -
      NF.dg (pres RD k sc) ν [up i, dn j] [dn j, up i] ([([], .dot (up i), [dn j])] ++ xLay (up i) (dn j)) ∈
        LeL RD k sc ν [up i, dn j] [dn j, up i] 0 := by
  xnormQ
  mswapQ 2
  mmodQ 1 [dn j] [dn j] (dsUp0 _ j i)
  mswapQ 0
  exact leL_sub_self _

theorem dsDnUp0 (ν : X) (i j : I) :
    NF.dg (pres RD k sc) ν [dn j, up i] [up i, dn j] (xLay (dn j) (up i) ++ [([], .dot (up i), [dn j])]) -
      NF.dg (pres RD k sc) ν [dn j, up i] [up i, dn j] ([([dn j], .dot (up i), [])] ++ xLay (dn j) (up i)) ∈
        LeL RD k sc ν [dn j, up i] [up i, dn j] 0 := by
  xnormQ
  mswapQ 2
  mmodQ 1 [dn j] [dn j] (dsUp1 _ i j)
  mswapQ 0
  exact leL_sub_self _

theorem dsDnUp1 (ν : X) (i j : I) :
    NF.dg (pres RD k sc) ν [dn j, up i] [up i, dn j] (xLay (dn j) (up i) ++ [([up i], .dot (dn j), [])]) -
      NF.dg (pres RD k sc) ν [dn j, up i] [up i, dn j] ([([], .dot (dn j), [up i])] ++ xLay (dn j) (up i)) ∈
        LeL RD k sc ν [dn j, up i] [up i, dn j] 0 := by
  xnormQ
  mswapQ 2; mswapQ 1
  matQ 0 [dn j, up i] [] (dg_dot_cupUp RD k sc j _)
  mmodQ 1 [dn j] [dn j] (leL_sub_comm (dsUp0 _ i j))
  matQ 2 [] [up i, dn j] (dg_dot_cap_up RD k sc _ j).symm
  mswapQ 1; mswapQ 0
  exact leL_sub_self _

section DnDn

variable [DecidableEq I]

theorem dsDn0 (hr : ∀ i, sc.r i = 1) (ν : X) (i j : I) :
    NF.dg (pres RD k sc) ν [dn i, dn j] [dn j, dn i] (xLay (dn i) (dn j) ++ [([], .dot (dn j), [dn i])]) -
      NF.dg (pres RD k sc) ν [dn i, dn j] [dn j, dn i] ([([dn i], .dot (dn j), [])] ++ xLay (dn i) (dn j)) ∈
        LeL RD k sc ν [dn i, dn j] [dn j, dn i] 0 := by
  have h := omega_transport hr (ν := -ν) (by schain) (by schain)
    (by simp [Sig.sgnS, Sig.sgnSh, mul_comm]) (dsUp0 (sc := CLQ.thetaScalars RD sc) (-ν) i j)
  rw [neg_neg] at h
  exact h

theorem dsDn1 (hr : ∀ i, sc.r i = 1) (ν : X) (i j : I) :
    NF.dg (pres RD k sc) ν [dn i, dn j] [dn j, dn i] (xLay (dn i) (dn j) ++ [([dn j], .dot (dn i), [])]) -
      NF.dg (pres RD k sc) ν [dn i, dn j] [dn j, dn i] ([([], .dot (dn i), [dn j])] ++ xLay (dn i) (dn j)) ∈
        LeL RD k sc ν [dn i, dn j] [dn j, dn i] 0 := by
  have h := omega_transport hr (ν := -ν) (by schain) (by schain)
    (by simp [Sig.sgnS, Sig.sgnSh, mul_comm]) (dsUp1 (sc := CLQ.thetaScalars RD sc) (-ν) i j)
  rw [neg_neg] at h
  exact h

/-- **Dots slide through every crossing modulo diagrams without crossings** (a dot on the left
upper strand). -/
theorem ds0 (hr : ∀ i, sc.r i = 1) (ν : X) (l₁ l₂ : Letter I) :
    NF.dg (pres RD k sc) ν [l₁, l₂] [l₂, l₁] (xLay l₁ l₂ ++ [([], .dot l₂, [l₁])]) -
      NF.dg (pres RD k sc) ν [l₁, l₂] [l₂, l₁] ([([l₁], .dot l₂, [])] ++ xLay l₁ l₂) ∈
        LeL RD k sc ν [l₁, l₂] [l₂, l₁] 0 := by
  obtain ⟨_ | _, i⟩ := l₁ <;> obtain ⟨_ | _, j⟩ := l₂
  · exact dsDn0 hr ν i j
  · exact dsDnUp0 ν j i
  · exact dsUpDn0 ν i j
  · exact dsUp0 ν i j

/-- **Dots slide through every crossing modulo diagrams without crossings** (a dot on the right
upper strand). -/
theorem ds1 (hr : ∀ i, sc.r i = 1) (ν : X) (l₁ l₂ : Letter I) :
    NF.dg (pres RD k sc) ν [l₁, l₂] [l₂, l₁] (xLay l₁ l₂ ++ [([l₂], .dot l₁, [])]) -
      NF.dg (pres RD k sc) ν [l₁, l₂] [l₂, l₁] ([([], .dot l₁, [l₂])] ++ xLay l₁ l₂) ∈
        LeL RD k sc ν [l₁, l₂] [l₂, l₁] 0 := by
  obtain ⟨_ | _, i⟩ := l₁ <;> obtain ⟨_ | _, j⟩ := l₂
  · exact dsDn1 hr ν i j
  · exact dsDnUp1 ν j i
  · exact dsUpDn1 ν i j
  · exact dsUp1 ν i j

end DnDn

/-! ## Reidemeister 2 modulo lower terms -/

theorem leL_comp0 {ν : X} {s t r : List (Letter I)} {f g}
    (hf : f ∈ LeL RD k sc ν s t 0) (hg : g ∈ LeL RD k sc ν t r 0) : f ≫ g ∈ LeL RD k sc ν s r 0 := by
  have := leL_comp hf hg; rwa [Nat.add_zero] at this

theorem leL_mul_mem {ν : X} {s : List (Letter I)} (a b : End ((pres RD k sc).obj (ob RD ν s)))
    (ha : a ∈ LeL RD k sc ν s s 0) (hb : b ∈ LeL RD k sc ν s s 0) : a * b ∈ LeL RD k sc ν s s 0 := by
  rw [End.mul_def]; exact leL_comp0 hb ha

theorem one_mem_leL {ν : X} {s : List (Letter I)} :
    (1 : End ((pres RD k sc).obj (ob RD ν s))) ∈ LeL RD k sc ν s s 0 := by
  rw [End.one_def, ← NF.dg_nil]; exact dg_mem_leL le_rfl

theorem r2Up (ν : X) (i j : I) :
    NF.dg (pres RD k sc) ν [up i, up j] [up i, up j] (xLay (up i) (up j) ++ xLay (up j) (up i)) ∈
      LeL RD k sc ν [up i, up j] [up i, up j] 1 := by
  simp only [xLay_up_up, List.singleton_append]
  rcases eq_or_ne i j with rfl | h
  · rw [dg_sqEq]; exact Submodule.zero_mem _
  · rw [dg_sqNe RD k sc ν i j h]
    refine leL_mono (Nat.zero_le 1) (ncEval_mem one_mem_leL leL_mul_mem _ (fun a => ?_) _)
    fin_cases a <;> exact dg_mem_leL (by simp)

theorem r2UpDn (ν : X) (i j : I) :
    NF.dg (pres RD k sc) ν [up i, dn j] [up i, dn j] (xLay (up i) (dn j) ++ xLay (dn j) (up i)) ∈
      LeL RD k sc ν [up i, dn j] [up i, dn j] 1 := by
  simp only [xLay_up_dn, xLay_dn_up]
  by_cases h : i = j
  · subst h
    have e := (dg_decompEF RD k sc i ν).symm
    rw [neg_add_eq_sub, sub_eq_iff_eq_add, ← sub_eq_iff_eq_add'] at e
    rw [← e]
    refine Submodule.sub_mem _ (Submodule.sum_mem _ fun f _ => Submodule.sum_mem _ fun g _ => ?_)
      (dg_mem_leL (by simp))
    refine leL_mono (Nat.zero_le 1) (leL_comp0 (dg_mem_leL ?_)
      (leL_comp0 (isBub_mem_leL (ccwU_isBub _ _)) (dg_mem_leL ?_)))
    · simp [dotCapEFLs, ccnt_cons, ccnt_append, ccnt_replicate_dot, Shape.isCross]
    · simp [cupDotEFLs, ccnt_cons, ccnt_replicate_dot, Shape.isCross]
  · rw [dg_downupEF RD k sc i j h]; exact Submodule.smul_mem _ _ (dg_mem_leL (by simp))

theorem r2DnUp (ν : X) (i j : I) :
    NF.dg (pres RD k sc) ν [dn j, up i] [dn j, up i] (xLay (dn j) (up i) ++ xLay (up i) (dn j)) ∈
      LeL RD k sc ν [dn j, up i] [dn j, up i] 1 := by
  simp only [xLay_up_dn, xLay_dn_up]
  by_cases h : i = j
  · subst h
    have e := (dg_decompFE RD k sc i ν).symm
    rw [neg_add_eq_sub, sub_eq_iff_eq_add, ← sub_eq_iff_eq_add'] at e
    rw [← e]
    refine Submodule.sub_mem _ (Submodule.sum_mem _ fun f _ => Submodule.sum_mem _ fun g _ => ?_)
      (dg_mem_leL (by simp))
    refine leL_mono (Nat.zero_le 1) (leL_comp0 (dg_mem_leL ?_)
      (leL_comp0 (isBub_mem_leL (cwU_isBub _ _)) (dg_mem_leL ?_)))
    · simp [dotCapFELs, ccnt_cons, ccnt_append, ccnt_replicate_dot, Shape.isCross]
    · simp [cupDotFELs, ccnt_cons, ccnt_replicate_dot, Shape.isCross]
  · rw [dg_downupFE RD k sc j i (Ne.symm h)]; exact Submodule.smul_mem _ _ (dg_mem_leL (by simp))

/-! ## Reidemeister 3 modulo lower terms -/

/-- **The braid relation on upward strands modulo diagrams without crossings** (KL III
`eq_r3_easy-gen`, `eq_r3_hard-gen`: the correction term of the latter is a polynomial in dots). -/
theorem r3upMod (ν : X) (c d e : I) :
    NF.dg (pres RD k sc) ν [up c, up d, up e] [up e, up d, up c]
        [([], .cross true c d, [up e]), ([up d], .cross true c e, []), ([], .cross true d e, [up c])] -
      NF.dg (pres RD k sc) ν [up c, up d, up e] [up e, up d, up c]
        [([up c], .cross true d e, []), ([], .cross true c e, [up d]), ([up e], .cross true c d, [])] ∈
      LeL RD k sc ν [up c, up d, up e] [up e, up d, up c] 0 := by
  by_cases h : c = e ∧ c ≠ d
  · obtain ⟨rfl, hcd⟩ := h
    have key := KLR.Diagram.braidQ_at (CL.qCL sc) (u := []) (v := []) hcd
      (KLR.Diagram.braidL c d c) (KLR.Diagram.braidR c d c) (KLR.Diagram.E0 c d c)
      (KLR.Diagram.E1 c d c) (KLR.Diagram.E2 c d c) rfl rfl rfl rfl rfl
    have key' := congrArg (functorEndAlg k (upFunctor RD k sc ν) _) key
    rw [map_sub, AlgHom.map_ncEval] at key'
    simp only [functorEndAlg, AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
      upFunctor_diag, upDiag_eq_dg] at key'
    refine (congrArg (· ∈ _) key').mpr (ncEval_mem one_mem_leL leL_mul_mem _ (fun a => ?_) _)
    fin_cases a <;>
    · simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, upFunctor_diag, upDiag_eq_dg]
      exact dg_mem_leL (by simp [ccnt, Shape.isCross, KLR.Diagram.dl, upLD, upShape])
  · exact leL_sub_of_eq (dg_braid RD k sc ν c d e h)

/-- **The outer mixed Reidemeister 3 move** (`F_j E_i E_k`), modulo diagrams with fewer
crossings, for all labels (for `i = j ≠ k` the rotation of the correction term of the braid
relation has no crossings). -/
theorem r3outRMod (i k' j : I) (μ : X) :
    NF.dg (pres RD k sc) μ [dn j, up i, up k'] [up k', up i, dn j]
      ([([dn j], .cross true i k', [])] ++ (crossrL k' j).map (whL [] [up i]) ++
        (crossrL i j).map (whL [up k'] [])) -
    NF.dg (pres RD k sc) μ [dn j, up i, up k'] [up k', up i, dn j]
      ((crossrL i j).map (whL [] [up k']) ++ (crossrL k' j).map (whL [up i] []) ++
        [([], .cross true i k', [dn j])]) ∈ LeL RD k sc μ [dn j, up i, up k'] [up k', up i, dn j] 2 := by
  dnorm
  mswapQ 3; mswapQ 4; mswapQ 2; mswapQ 3; mswapQ 1; mswapQ 2; mswapQ 5; mswapQ 4
  matQ 3 [dn j, up k'] [up i, dn j] (NF.dg_zigL' (pres RD k sc) _ (up j))
  mswapQ 0
  mmodQ 1 [dn j] [dn j] (r3upMod _ i k' j)
  refine leL_sub_comm ?_
  mswapQ 2; mswapQ 3; mswapQ 1; mswapQ 2; mswapQ 0; mswapQ 1; mswapQ 4; mswapQ 3
  matQ 2 [dn j, up i] [up k', dn j] (NF.dg_zigL' (pres RD k sc) _ (up j))
  mswapQ 3
  exact leL_sub_self _

/-- The outer mixed Reidemeister 3 move `E_i E_k F_j`, modulo diagrams with fewer crossings. -/
theorem r3outLMod (i k' j : I) (μ : X) :
    NF.dg (pres RD k sc) μ [up i, up k', dn j] [dn j, up k', up i]
      ((crosslL k' j).map (whL [up i] []) ++ (crosslL i j).map (whL [] [up k']) ++
        [([dn j], .cross true i k', [])]) -
    NF.dg (pres RD k sc) μ [up i, up k', dn j] [dn j, up k', up i]
      ([([], .cross true i k', [dn j])] ++ (crosslL i j).map (whL [up k'] []) ++
        (crosslL k' j).map (whL [] [up i])) ∈ LeL RD k sc μ [up i, up k', dn j] [dn j, up k', up i] 2 := by
  dnorm
  mswapQ 2; mswapQ 3; mswapQ 1; mswapQ 2; mswapQ 0; mswapQ 1; mswapQ 4; mswapQ 3
  matQ 2 [dn j, up i] [up k', dn j] (NF.dg_zigR' (pres RD k sc) _ (dn j))
  mswapQ 3
  mmodQ 1 [dn j] [dn j] (r3upMod _ j i k')
  refine leL_sub_comm ?_
  mswapQ 3; mswapQ 4; mswapQ 2; mswapQ 3; mswapQ 1; mswapQ 2; mswapQ 0; mswapQ 5; mswapQ 4
  matQ 3 [dn j, up k'] [up i, dn j] (NF.dg_zigR' (pres RD k sc) _ (dn j))
  exact leL_sub_self _

/-- **The two descriptions of the sideways crossing `F_i E_j → E_j F_i`**: the rotation of the
downward crossing (the orientation reversal of `crossl_{ij}`) is `crossr_{ji}` (cyclicity). -/
theorem dg_wls_crosslL (i j : I) (μ : X) :
    NF.dg (pres RD k sc) μ [dn i, up j] [up j, dn i]
      [([], .cup (up j), [dn i, up j]), ([up j], .cross false j i, [up j]),
        ([up j, dn i], .cap (up j), [])] =
    ((((sc.t i j))⁻¹ : kˣ) : k) • NF.dg (pres RD k sc) μ [dn i, up j] [up j, dn i] (crossrL j i) := by
  refine Eq.trans (NF.dg_step_at_smul _ 1 [up j] [up j] _ (dg_cycCrossR RD k sc j i _)
    (by (try dnorm); schain) (by (try dnorm); schain) (by dnorm)) ?_
  try dnorm
  congr 1
  dswapQ 0; dswapQ 1; dswapQ 2; dswapQ 3
  datQ 4 [] [dn i, dn j, up j] (NF.dg_zigL' (pres RD k sc) _ (up j))
  dswapQ 3; dswapQ 2; dswapQ 1
  datQ 0 [dn i] [] (NF.dg_zigL' (pres RD k sc) _ (up j))

/-- **The two descriptions of the sideways crossing `E_j F_i → F_i E_j`**. -/
theorem dg_wls_crossrL (i j : I) (μ : X) :
    NF.dg (pres RD k sc) μ [up j, dn i] [dn i, up j]
      [([up j, dn i], .cup (dn j), []), ([up j], .cross false i j, [up j]),
        ([], .cap (dn j), [dn i, up j])] =
    ((((sc.t i j))⁻¹ : kˣ) : k) • NF.dg (pres RD k sc) μ [up j, dn i] [dn i, up j] (crosslL j i) := by
  refine Eq.trans (NF.dg_step_at_smul _ 1 [up j] [up j] _ (dg_cycCrossL RD k sc i j _)
    (by (try dnorm); schain) (by (try dnorm); schain) (by dnorm)) ?_
  try dnorm
  congr 1
  dswapQ 0; dswapQ 1; dswapQ 2; dswapQ 3
  datQ 4 [up j, dn j, dn i] [] (NF.dg_zigR' (pres RD k sc) _ (dn j))
  dswapQ 3; dswapQ 2; dswapQ 1
  datQ 0 [] [dn i] (NF.dg_zigR' (pres RD k sc) _ (dn j))

/-- `crossr_{ji}` is `t_{ij}` times the rotation of the downward crossing (`dg_wls_crosslL`). -/
theorem dg_crossrL_eq_smul_wls (i j : I) (μ : X) :
    NF.dg (pres RD k sc) μ [dn i, up j] [up j, dn i] (crossrL j i) =
      (sc.t i j : k) • NF.dg (pres RD k sc) μ [dn i, up j] [up j, dn i]
        [([], .cup (up j), [dn i, up j]), ([up j], .cross false j i, [up j]),
          ([up j, dn i], .cap (up j), [])] := by
  rw [dg_wls_crosslL, smul_smul, Units.mul_inv, one_smul]

/-- `crossl_{ji}` is `t_{ij}` times the rotation of the downward crossing (`dg_wls_crossrL`). -/
theorem dg_crosslL_eq_smul_wls (i j : I) (μ : X) :
    NF.dg (pres RD k sc) μ [up j, dn i] [dn i, up j] (crosslL j i) =
      (sc.t i j : k) • NF.dg (pres RD k sc) μ [up j, dn i] [dn i, up j]
        [([up j, dn i], .cup (dn j), []), ([up j], .cross false i j, [up j]),
          ([], .cap (dn j), [dn i, up j])] := by
  rw [dg_wls_crossrL, smul_smul, Units.mul_inv, one_smul]

theorem sub_mem_of_smul₂ {M : Type*} [AddCommGroup M] [Module k M] {S : Submodule k M}
    (a b : k) {x x' y y' : M} (hx : x = a • b • x') (hy : y = a • b • y') (h : x' - y' ∈ S) :
    x - y ∈ S := by
  rw [hx, hy, ← smul_sub, ← smul_sub]; exact S.smul_mem _ (S.smul_mem _ h)

theorem sub_smul_mem_of_left {M : Type*} [AddCommGroup M] [Module k M] {S : Submodule k M}
    (a : k) {x x' y : M} (hx : x = a • x') (h : x' - y ∈ S) : x - a • y ∈ S := by
  rw [hx, ← smul_sub]; exact S.smul_mem _ h

theorem sub_smul_mem_of_right {M : Type*} [AddCommGroup M] [Module k M] {S : Submodule k M}
    (a : kˣ) {x y y' : M} (hy : y = (a : k) • y') (h : x - y' ∈ S) :
    x - ((a⁻¹ : kˣ) : k) • y ∈ S := by
  rwa [hy, smul_smul, Units.inv_mul, one_smul]

/-- `datSQ n u v E`: in a goal `dg μ s₀ t₀ L = c • y`, rewrite `L` with the local equation
`E : dg ν s t A = c • dg ν s t B` placed between the strands `u` and `v` (`A` starting at the
layer `n`), and cancel `c`. -/
macro "datSQ " n:term:max u:term:max v:term:max E:term:max : tactic => `(tactic| (
  refine Eq.trans (NF.dg_step_at_smul _ $n $u $v _ $E (by (try dnorm); schain)
    (by (try dnorm); schain) (by dnorm)) ?_
  try dnorm
  congr 1))

theorem r3_EEE (ν : X) (c d e : I) :
    NF.dg (pres RD k sc) ν [up c, up d, up e] [up e, up d, up c] (r3L (up c) (up d) (up e)) -
      NF.dg (pres RD k sc) ν [up c, up d, up e] [up e, up d, up c] (r3R (up c) (up d) (up e)) ∈
        LeL RD k sc ν [up c, up d, up e] [up e, up d, up c] 2 :=
  leL_mono (Nat.zero_le 2) (r3upMod ν c d e)

theorem bubLU_mem_leL {μ : X} {l : Letter I} {β : End ((pres RD k sc).obj (ob RD (wt RD μ [l]) []))}
    (hβ : IsBub RD k sc (wt RD μ [l]) β) : NF.bubLU (pres RD k sc) μ l β ∈ LeL RD k sc μ [l] [l] 0 :=
  plcL_leL (u := []) (v := [l]) (s := []) (t := []) (isBub_mem_leL hβ)

theorem bubRU_mem_leL {μ : X} {l : Letter I} {β : End ((pres RD k sc).obj (ob RD μ []))}
    (hβ : IsBub RD k sc μ β) : NF.bubRU (pres RD k sc) μ l β ∈ LeL RD k sc μ [l] [l] 0 :=
  plcL_leL (u := [l]) (v := []) (s := []) (t := []) (isBub_mem_leL hβ)

theorem sigma1Term_mem (lam : X) (i : I) (f₁ f₂ f₃ f₄ : ℕ) :
    sigma1Term RD k sc lam i f₁ f₂ f₃ f₄ ∈ LeL RD k sc lam [up i, dn i, up i] [up i, dn i, up i] 0 := by
  unfold sigma1Term
  have h1 := bubLU_mem_leL (RD := RD) (k := k) (sc := sc) (μ := lam) (l := up i)
    (ccwU_isBub (lam := wt RD lam [up i]) i (-ip RD i lam - 3 + f₄))
  refine leL_comp0 (dg_mem_leL ?_) (leL_comp0 h1
    (leL_comp0 (dg_mem_leL ?_) (leL_comp0 (dg_mem_leL ?_) (dg_mem_leL ?_))))
  all_goals simp [ccnt_cons, ccnt_append, ccnt_replicate_dot, Shape.isCross]

theorem sigma2Term_mem (lam : X) (i : I) (g₁ g₂ g₃ g₄ : ℕ) :
    sigma2Term RD k sc lam i g₁ g₂ g₃ g₄ ∈ LeL RD k sc lam [up i, dn i, up i] [up i, dn i, up i] 0 := by
  unfold sigma2Term
  have h1 := bubRU_mem_leL (RD := RD) (k := k) (sc := sc) (μ := lam) (l := up i)
    (cwU_isBub (lam := lam) i (ip RD i lam - 1 + g₄))
  refine leL_comp0 (dg_mem_leL ?_) (leL_comp0 h1
    (leL_comp0 (dg_mem_leL ?_) (leL_comp0 (dg_mem_leL ?_) (dg_mem_leL ?_))))
  all_goals simp [ccnt_cons, ccnt_append, ccnt_replicate_dot, Shape.isCross]

theorem r3_EFE (ν : X) (i j k' : I) :
    NF.dg (pres RD k sc) ν [up i, dn j, up k'] [up k', dn j, up i] (r3L (up i) (dn j) (up k')) -
      NF.dg (pres RD k sc) ν [up i, dn j, up k'] [up k', dn j, up i] (r3R (up i) (dn j) (up k')) ∈
        LeL RD k sc ν [up i, dn j, up k'] [up k', dn j, up i] 2 := by
  have e₁ : r3L (up i) (dn j) (up k') = r3mixL i j k' := by
    simp [r3L, r3mixL, xLay_up_dn, xLay_dn_up, xLay_up_up]
  have e₂ : r3R (up i) (dn j) (up k') = r3mixR i j k' := by
    simp [r3R, r3mixR, xLay_up_dn, xLay_dn_up, xLay_up_up]
  rw [e₁, e₂]
  by_cases h : i = j ∧ j = k'
  · obtain ⟨rfl, rfl⟩ := h
    rw [prop35_b]
    refine leL_mono (Nat.zero_le 2) (Submodule.add_mem _ ?_ ?_)
    · split_ifs
      · exact Submodule.sum_mem _ fun x _ => Submodule.sum_mem _ fun z _ =>
          Submodule.sum_mem _ fun y _ => sigma1Term_mem _ _ _ _ _ _
      · exact Submodule.zero_mem _
    · split_ifs
      · exact Submodule.sum_mem _ fun x _ => Submodule.sum_mem _ fun z _ =>
          Submodule.sum_mem _ fun y _ => sigma2Term_mem _ _ _ _ _ _
      · exact Submodule.zero_mem _
  · exact leL_sub_of_eq (prop35_a RD k sc i j k' h ν)

theorem r3_FEE (ν : X) (j i k' : I) :
    NF.dg (pres RD k sc) ν [dn j, up i, up k'] [up k', up i, dn j] (r3L (dn j) (up i) (up k')) -
      NF.dg (pres RD k sc) ν [dn j, up i, up k'] [up k', up i, dn j] (r3R (dn j) (up i) (up k')) ∈
        LeL RD k sc ν [dn j, up i, up k'] [up k', up i, dn j] 2 := by
  have h := leL_sub_comm (r3outRMod (RD := RD) (k := k) (sc := sc) i k' j ν)
  simpa [r3L, r3R, xLay_up_dn, xLay_dn_up, xLay_up_up] using h

theorem r3_EEF (ν : X) (i k' j : I) :
    NF.dg (pres RD k sc) ν [up i, up k', dn j] [dn j, up k', up i] (r3L (up i) (up k') (dn j)) -
      NF.dg (pres RD k sc) ν [up i, up k', dn j] [dn j, up k', up i] (r3R (up i) (up k') (dn j)) ∈
        LeL RD k sc ν [up i, up k', dn j] [dn j, up k', up i] 2 := by
  have h := leL_sub_comm (r3outLMod (RD := RD) (k := k) (sc := sc) i k' j ν)
  simpa [r3L, r3R, xLay_up_dn, xLay_dn_up, xLay_up_up] using h

section R3Omega

variable [DecidableEq I]

theorem r3_FFF (hr : ∀ i, sc.r i = 1) (ν : X) (c d e : I) :
    NF.dg (pres RD k sc) ν [dn c, dn d, dn e] [dn e, dn d, dn c] (r3L (dn c) (dn d) (dn e)) -
      NF.dg (pres RD k sc) ν [dn c, dn d, dn e] [dn e, dn d, dn c] (r3R (dn c) (dn d) (dn e)) ∈
        LeL RD k sc ν [dn c, dn d, dn e] [dn e, dn d, dn c] 2 := by
  have h := omega_transport hr (ν := -ν) (sChain_r3L _ _ _) (sChain_r3R _ _ _) (sgnS_r3 _ _ _)
    (r3_EEE (sc := CLQ.thetaScalars RD sc) (-ν) c d e)
  rw [neg_neg] at h
  exact h

theorem r3_FEF (hr : ∀ i, sc.r i = 1) (ν : X) (i j k' : I) :
    NF.dg (pres RD k sc) ν [dn i, up j, dn k'] [dn k', up j, dn i] (r3L (dn i) (up j) (dn k')) -
      NF.dg (pres RD k sc) ν [dn i, up j, dn k'] [dn k', up j, dn i] (r3R (dn i) (up j) (dn k')) ∈
        LeL RD k sc ν [dn i, up j, dn k'] [dn k', up j, dn i] 2 := by
  have h := omega_transport hr (ν := -ν) (sChain_r3L _ _ _) (sChain_r3R _ _ _) (sgnS_r3 _ _ _)
    (r3_EFE (sc := CLQ.thetaScalars RD sc) (-ν) i j k')
  rw [neg_neg] at h
  simp only [r3L, r3R]
  xnormQ
  refine sub_mem_of_smul₂ (sc.t i j : k) (sc.t k' j : k) ?_ ?_ h
  · datSQ 0 [] [dn k'] (dg_crossrL_eq_smul_wls i j _)
    datSQ 4 [] [dn i] (dg_crosslL_eq_smul_wls k' j _)
  · rw [smul_comm]
    datSQ 0 [dn i] [] (dg_crosslL_eq_smul_wls k' j _)
    datSQ 4 [dn k'] [] (dg_crossrL_eq_smul_wls i j _)

theorem r3_FFE (hr : ∀ i, sc.r i = 1) (ν : X) (i k' j : I) :
    NF.dg (pres RD k sc) ν [dn i, dn k', up j] [up j, dn k', dn i] (r3L (dn i) (dn k') (up j)) -
      NF.dg (pres RD k sc) ν [dn i, dn k', up j] [up j, dn k', dn i] (r3R (dn i) (dn k') (up j)) ∈
        LeL RD k sc ν [dn i, dn k', up j] [up j, dn k', dn i] 2 := by
  have h := omega_transport hr (ν := -ν) (sChain_r3L _ _ _) (sChain_r3R _ _ _) (sgnS_r3 _ _ _)
    (r3_EEF (sc := CLQ.thetaScalars RD sc) (-ν) i k' j)
  rw [neg_neg] at h
  simp only [r3L, r3R]
  xnormQ
  refine sub_mem_of_smul₂ (sc.t i j : k) (sc.t k' j : k) ?_ ?_ h
  · datSQ 1 [dn k'] [] (dg_crossrL_eq_smul_wls i j _)
    datSQ 4 [] [dn i] (dg_crossrL_eq_smul_wls k' j _)
  · rw [smul_comm]
    datSQ 0 [dn i] [] (dg_crossrL_eq_smul_wls k' j _)
    datSQ 3 [] [dn k'] (dg_crossrL_eq_smul_wls i j _)

theorem r3_EFF (hr : ∀ i, sc.r i = 1) (ν : X) (j i k' : I) :
    NF.dg (pres RD k sc) ν [up j, dn i, dn k'] [dn k', dn i, up j] (r3L (up j) (dn i) (dn k')) -
      NF.dg (pres RD k sc) ν [up j, dn i, dn k'] [dn k', dn i, up j] (r3R (up j) (dn i) (dn k')) ∈
        LeL RD k sc ν [up j, dn i, dn k'] [dn k', dn i, up j] 2 := by
  have h := omega_transport hr (ν := -ν) (sChain_r3L _ _ _) (sChain_r3R _ _ _) (sgnS_r3 _ _ _)
    (r3_FEE (sc := CLQ.thetaScalars RD sc) (-ν) j i k')
  rw [neg_neg] at h
  simp only [r3L, r3R]
  xnormQ
  refine sub_mem_of_smul₂ (sc.t i j : k) (sc.t k' j : k) ?_ ?_ h
  · datSQ 0 [] [dn k'] (dg_crosslL_eq_smul_wls i j _)
    datSQ 3 [dn i] [] (dg_crosslL_eq_smul_wls k' j _)
  · rw [smul_comm]
    datSQ 1 [] [dn i] (dg_crosslL_eq_smul_wls k' j _)
    datSQ 4 [dn k'] [] (dg_crosslL_eq_smul_wls i j _)

/-- **Reidemeister 3 modulo lower terms, for all orientations and labels**: the two composites
of three crossings `[l₁, l₂, l₃] → [l₃, l₂, l₁]` agree modulo diagrams with at most two
crossings. -/
theorem r3 (hr : ∀ i, sc.r i = 1) (ν : X) (l₁ l₂ l₃ : Letter I) :
    NF.dg (pres RD k sc) ν [l₁, l₂, l₃] [l₃, l₂, l₁] (r3L l₁ l₂ l₃) -
      NF.dg (pres RD k sc) ν [l₁, l₂, l₃] [l₃, l₂, l₁] (r3R l₁ l₂ l₃) ∈
        LeL RD k sc ν [l₁, l₂, l₃] [l₃, l₂, l₁] 2 := by
  obtain ⟨_ | _, a⟩ := l₁ <;> obtain ⟨_ | _, b⟩ := l₂ <;> obtain ⟨_ | _, c⟩ := l₃
  · exact r3_FFF hr ν a b c
  · exact r3_FFE hr ν a b c
  · exact r3_FEF hr ν a b c
  · exact r3_FEE ν a b c
  · exact r3_EFF hr ν a b c
  · exact r3_EFE ν a b c
  · exact r3_EEF ν a b c
  · exact r3_EEE ν a b c

theorem r2Dn (hr : ∀ i, sc.r i = 1) (ν : X) (i j : I) :
    NF.dg (pres RD k sc) ν [dn i, dn j] [dn i, dn j] (xLay (dn i) (dn j) ++ xLay (dn j) (dn i)) ∈
      LeL RD k sc ν [dn i, dn j] [dn i, dn j] 1 := by
  have h := omega_transport_single hr (ν := -ν) ((sChain_xLay _ _).append (sChain_xLay _ _))
    (r2Up (sc := CLQ.thetaScalars RD sc) (-ν) i j)
  rw [neg_neg] at h
  exact h

/-- **Reidemeister 2 modulo lower terms, for all orientations and labels.** -/
theorem r2 (hr : ∀ i, sc.r i = 1) (ν : X) (l₁ l₂ : Letter I) :
    NF.dg (pres RD k sc) ν [l₁, l₂] [l₁, l₂] (xLay l₁ l₂ ++ xLay l₂ l₁) ∈ LeL RD k sc ν [l₁, l₂] [l₁, l₂] 1 := by
  obtain ⟨_ | _, a⟩ := l₁ <;> obtain ⟨_ | _, b⟩ := l₂
  · exact r2Dn hr ν a b
  · exact r2DnUp ν b a
  · exact r2UpDn ν a b
  · exact r2Up ν a b

end R3Omega

/-! ## Curls on cups and caps -/

theorem curlR_mem (ν : X) (i : I) : NF.dg (pres RD k sc) ν [up i] [up i]
      [([up i], .cup (up i), []), ([], .cross true i i, [dn i]), ([up i], .cap (dn i), [])] ∈
      LeL RD k sc ν [up i] [up i] 0 := by
  rw [dg_curlR]
  refine Submodule.neg_mem _ (Submodule.sum_mem _ fun f _ =>
    leL_comp0 (bubRU_mem_leL (cwU_isBub _ _)) ?_)
  rw [← NF.dotsU_eq]; unfold dots; rw [← NF.dg_of]; exact dg_mem_leL (by simp [ccnt_replicate_dot])

theorem curlL_mem (μ : X) (i : I) : NF.dg (pres RD k sc) μ [up i] [up i]
      [([], .cup (dn i), [up i]), ([dn i], .cross true i i, []), ([], .cap (up i), [up i])] ∈
      LeL RD k sc μ [up i] [up i] 0 := by
  rw [dg_curlL]
  refine Submodule.sum_mem _ fun f _ => leL_comp0 (bubLU_mem_leL (ccwU_isBub _ _)) ?_
  rw [← NF.dotsU_eq]; unfold dots; rw [← NF.dg_of]; exact dg_mem_leL (by simp [ccnt_replicate_dot])

/-- **A crossing of the two legs of a cup is a lower term** (curl relations of KL III
Definition 3.1 iv), rotated). -/
theorem cupCurl (ν : X) (l : Letter I) :
    NF.dg (pres RD k sc) ν [] [l.dual, l] ([([], .cup l, [])] ++ xLay l l.dual) ∈ LeL RD k sc ν [] [l.dual, l] 0 := by
  obtain ⟨_ | _, i⟩ := l
  · show NF.dg (pres RD k sc) ν [] [up i, dn i] ([([], .cup (dn i), [])] ++ xLay (dn i) (up i)) ∈ _
    xnormQ
    iswapQ 0
    have := dg_mem_ctx ν [([], .cup (up i), [])] [] [] [dn i] (curlL_mem (RD := RD) (k := k) (sc := sc) _ i)
      (by schain) (by schain)
    simpa using this
  · show NF.dg (pres RD k sc) ν [] [dn i, up i] ([([], .cup (up i), [])] ++ xLay (up i) (dn i)) ∈ _
    xnormQ
    iswapQ 0
    have := dg_mem_ctx ν [([], .cup (dn i), [])] [] [dn i] [] (curlR_mem (RD := RD) (k := k) (sc := sc) _ i)
      (by schain) (by schain)
    simpa using this

/-- **A crossing of the two legs of a cap is a lower term.** -/
theorem capCurl (ν : X) (l : Letter I) :
    NF.dg (pres RD k sc) ν [l, l.dual] [] (xLay l l.dual ++ [([], .cap l, [])]) ∈
      LeL RD k sc ν [l, l.dual] [] 0 := by
  obtain ⟨_ | _, i⟩ := l
  · show NF.dg (pres RD k sc) ν [dn i, up i] [] (xLay (dn i) (up i) ++ [([], .cap (dn i), [])]) ∈ _
    xnormQ
    iswapQ 2
    have := dg_mem_ctx ν [] [([], .cap (up i), [])] [dn i] [] (curlR_mem (RD := RD) (k := k) (sc := sc) _ i)
      (by schain) (by schain)
    simpa using this
  · show NF.dg (pres RD k sc) ν [up i, dn i] [] (xLay (up i) (dn i) ++ [([], .cap (up i), [])]) ∈ _
    xnormQ
    iswapQ 2
    have := dg_mem_ctx ν [] [([], .cap (dn i), [])] [] [dn i] (curlL_mem (RD := RD) (k := k) (sc := sc) _ i)
      (by schain) (by schain)
    simpa using this

/-! ## Pitchfork moves through caps and cups -/

theorem capPF_up_up (ν : X) (j i : I) :
    NF.dg (pres RD k sc) ν [dn j, up i, up j] [up i] ((xLay (dn j) (up i)).map (whL [] [up j]) ++
        [([up i], .cap (up j), [])]) -
      NF.dg (pres RD k sc) ν [dn j, up i, up j] [up i] ((xLay (up i) (up j)).map (whL [dn j] []) ++
        [([], .cap (up j), [up i])]) ∈ LeL RD k sc ν [dn j, up i, up j] [up i] 0 :=
  leL_sub_of_eq (by simpa using dg_pf_capUp RD k sc i j ν)

theorem capPF_dn_up (ν : X) (j i : I) :
    NF.dg (pres RD k sc) ν [up j, up i, dn j] [up i] ((xLay (up j) (up i)).map (whL [] [dn j]) ++
        [([up i], .cap (dn j), [])]) -
      NF.dg (pres RD k sc) ν [up j, up i, dn j] [up i] ((xLay (up i) (dn j)).map (whL [up j] []) ++
        [([], .cap (dn j), [up i])]) ∈ LeL RD k sc ν [up j, up i, dn j] [up i] 0 :=
  leL_sub_of_eq (by simpa using (dg_pf_capDn RD k sc i j ν).symm)

theorem cupPF_up_up (ν : X) (j i : I) :
    NF.dg (pres RD k sc) ν [up i] [up j, up i, dn j] ([([], .cup (up j), [up i])] ++
        (xLay (dn j) (up i)).map (whL [up j] [])) -
      NF.dg (pres RD k sc) ν [up i] [up j, up i, dn j] ([([up i], .cup (up j), [])] ++
        (xLay (up i) (up j)).map (whL [] [dn j])) ∈ LeL RD k sc ν [up i] [up j, up i, dn j] 0 :=
  leL_sub_of_eq (by simpa using dg_pf_cupUp RD k sc i j ν)

theorem cupPF_dn_up (ν : X) (j i : I) :
    NF.dg (pres RD k sc) ν [up i] [dn j, up i, up j] ([([], .cup (dn j), [up i])] ++
        (xLay (up j) (up i)).map (whL [dn j] [])) -
      NF.dg (pres RD k sc) ν [up i] [dn j, up i, up j] ([([up i], .cup (dn j), [])] ++
        (xLay (up i) (dn j)).map (whL [] [up j])) ∈ LeL RD k sc ν [up i] [dn j, up i, up j] 0 :=
  leL_sub_of_eq (by simpa using (dg_pf_cupDn RD k sc i j ν).symm)

theorem cupPF_up_dn (ν : X) (j i : I) :
    NF.dg (pres RD k sc) ν [dn i] [up j, dn i, dn j] ([([], .cup (up j), [dn i])] ++
        (xLay (dn j) (dn i)).map (whL [up j] [])) -
      (((sc.t i j)⁻¹ : kˣ) : k) • NF.dg (pres RD k sc) ν [dn i] [up j, dn i, dn j]
          ([([dn i], .cup (up j), [])] ++ (xLay (dn i) (up j)).map (whL [] [dn j])) ∈
        LeL RD k sc ν [dn i] [up j, dn i, dn j] 0 :=
  leL_sub_of_eq (by simpa using dg_pf_cupUp_down RD k sc i j ν)

section PFOmega

variable [DecidableEq I]

theorem capPF_dn_dn (hr : ∀ i, sc.r i = 1) (ν : X) (j i : I) :
    NF.dg (pres RD k sc) ν [up j, dn i, dn j] [dn i] ((xLay (up j) (dn i)).map (whL [] [dn j]) ++
        [([dn i], .cap (dn j), [])]) -
      (sc.t i j : k) • NF.dg (pres RD k sc) ν [up j, dn i, dn j] [dn i]
        ((xLay (dn i) (dn j)).map (whL [up j] []) ++ [([], .cap (dn j), [dn i])]) ∈
        LeL RD k sc ν [up j, dn i, dn j] [dn i] 0 := by
  have h := omega_transport hr (ν := -ν) (by simp only [xLay_dn_up, crossrL]; schain) (by schain)
    (by simp [xLay, crossrL, Sig.sgnS, Sig.sgnSh]) (capPF_up_up (sc := CLQ.thetaScalars RD sc) (-ν) j i)
  rw [neg_neg] at h
  xnormQ
  refine sub_smul_mem_of_left _ ?_ h
  datSQ 0 [] [dn j] (dg_crosslL_eq_smul_wls i j _)

theorem capPF_up_dn (hr : ∀ i, sc.r i = 1) (ν : X) (j i : I) :
    NF.dg (pres RD k sc) ν [dn j, dn i, up j] [dn i] ((xLay (dn j) (dn i)).map (whL [] [up j]) ++
        [([dn i], .cap (up j), [])]) -
      (((sc.t i j)⁻¹ : kˣ) : k) • NF.dg (pres RD k sc) ν [dn j, dn i, up j] [dn i]
        ((xLay (dn i) (up j)).map (whL [dn j] []) ++ [([], .cap (up j), [dn i])]) ∈
        LeL RD k sc ν [dn j, dn i, up j] [dn i] 0 := by
  have h := omega_transport hr (ν := -ν) (by schain) (by simp only [xLay_up_dn, crosslL]; schain)
    (by simp [xLay, crosslL, Sig.sgnS, Sig.sgnSh]) (capPF_dn_up (sc := CLQ.thetaScalars RD sc) (-ν) j i)
  rw [neg_neg] at h
  xnormQ
  refine sub_smul_mem_of_right (sc.t i j) ?_ h
  datSQ 0 [dn j] [] (dg_crossrL_eq_smul_wls i j _)

theorem cupPF_dn_dn (hr : ∀ i, sc.r i = 1) (ν : X) (j i : I) :
    NF.dg (pres RD k sc) ν [dn i] [dn j, dn i, up j] ([([], .cup (dn j), [dn i])] ++
        (xLay (up j) (dn i)).map (whL [dn j] [])) -
      (sc.t i j : k) • NF.dg (pres RD k sc) ν [dn i] [dn j, dn i, up j] ([([dn i], .cup (dn j), [])] ++
        (xLay (dn i) (dn j)).map (whL [] [up j])) ∈ LeL RD k sc ν [dn i] [dn j, dn i, up j] 0 := by
  have h := omega_transport hr (ν := -ν) (by simp only [xLay_dn_up, crossrL]; schain) (by schain)
    (by simp [xLay, crossrL, Sig.sgnS, Sig.sgnSh]) (cupPF_up_up (sc := CLQ.thetaScalars RD sc) (-ν) j i)
  rw [neg_neg] at h
  xnormQ
  refine sub_smul_mem_of_left _ ?_ h
  datSQ 1 [dn j] [] (dg_crosslL_eq_smul_wls i j _)

/-- **Pitchfork through a cap**: a strand crossing the left leg of a cap below it equals the
strand crossing the right leg, up to a unit (modulo lower terms; in fact exactly). In `U_Q(g)`
the unit is `1` unless `m` is downward and the crossings are the sideways ones and a downward
crossing, when it is `t_{ij}^{±1}` (cyclicity of the downward crossing). -/
theorem capPF (hr : ∀ i, sc.r i = 1) (ν : X) (l m : Letter I) :
    ∃ c : kˣ,
      NF.dg (pres RD k sc) ν [l.dual, m, l] [m] ((xLay l.dual m).map (whL [] [l]) ++ [([m], .cap l, [])]) -
        (c : k) • NF.dg (pres RD k sc) ν [l.dual, m, l] [m]
          ((xLay m l).map (whL [l.dual] []) ++ [([], .cap l, [m])]) ∈
        LeL RD k sc ν [l.dual, m, l] [m] 0 := by
  obtain ⟨_ | _, j⟩ := l <;> obtain ⟨_ | _, i⟩ := m
  · exact ⟨sc.t i j, capPF_dn_dn hr ν j i⟩
  · exact ⟨1, by rw [Units.val_one, one_smul]; exact capPF_dn_up ν j i⟩
  · exact ⟨(sc.t i j)⁻¹, capPF_up_dn hr ν j i⟩
  · exact ⟨1, by rw [Units.val_one, one_smul]; exact capPF_up_up ν j i⟩

/-- **Pitchfork through a cup**: a strand crossing the right leg of a cup to its left equals the
strand crossing the left leg of the cup to its right, up to a unit (as for `capPF`). -/
theorem cupPF (hr : ∀ i, sc.r i = 1) (ν : X) (l m : Letter I) :
    ∃ c : kˣ,
      NF.dg (pres RD k sc) ν [m] [l, m, l.dual] ([([], .cup l, [m])] ++ (xLay l.dual m).map (whL [l] [])) -
        (c : k) • NF.dg (pres RD k sc) ν [m] [l, m, l.dual]
          ([([m], .cup l, [])] ++ (xLay m l).map (whL [] [l.dual])) ∈
        LeL RD k sc ν [m] [l, m, l.dual] 0 := by
  obtain ⟨_ | _, j⟩ := l <;> obtain ⟨_ | _, i⟩ := m
  · exact ⟨sc.t i j, cupPF_dn_dn hr ν j i⟩
  · exact ⟨1, by rw [Units.val_one, one_smul]; exact cupPF_dn_up ν j i⟩
  · exact ⟨(sc.t i j)⁻¹, cupPF_up_dn ν j i⟩
  · exact ⟨1, by rw [Units.val_one, one_smul]; exact cupPF_up_up ν j i⟩

end PFOmega

end Categorification.KL3.Diagram.CLQ
