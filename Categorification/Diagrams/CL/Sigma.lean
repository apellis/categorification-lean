/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.CL.RescaleR

/-!
# The isomorphism `Σ : U(sl_n) ≅ U_Q(sl_n)` with signed scalars

M. Khovanov, A. Lauda, *A categorification of quantum `sl(n)`*, arXiv:0807.3250v1, §4.2.1
(TeX label `subsubsec_isom`, "The 2-isomorphism `Σ : U → U→`"), as corrected in the erratum
(Quantum Topol. 2 (2011), 97–99, p. 99: "The only part of the isomorphism `Σ` that needs to be
modified is the image of caps and cups"); S. Cautis, A. D. Lauda, arXiv:1111.1431v3.

We construct `Σ` as a rescaling isomorphism (`Categorification.Diagrams.CL.Rescale`)
`sigmaEquiv : U_{kl}(sl_n) ≅ U_{Q}(sl_n)` from KL III's `U(sl_n)` (`presCL_kl`) to CL's `U_Q` with
the signed scalars `Sln.slnScalars` (`t_{ij} = i - j` for adjacent `i, j`, `s = 0`, `r = 1`),
which has the relations of the consistent variant `presSignedQT'` of the erratum's revised
Definition 4.1 away from the adjacent crossing-cyclicity relations
(`Sln.relationCL_sln_eq_relationQT'`).

## Conventions

Our vertices are `Fin m` (`n = m + 1`); KL number them `1, …, n - 1` with the orientation
`1 → 2 → ⋯ → n - 1` (eq. `eq_oriented_graph`), so KL's vertex `i + 1` is our `i`, and KL's sign
`(-1)^{i_KL}` is `d_i = (-1)^{i+1}` (`sigmaSign`).

## The datum and its comparison with KL III and the erratum

* **Dots** (`sigmaDatum_dot`): `Σ(x_i) = d_i x_i` on every strand labelled `i` — KL III's rule
  for upward dots; the downward dots are forced to be scaled by the same `d_i` (by `eq_cyclic_dot`).
* **Upward crossings** (`sigmaDatum_cross`): the crossing with bottom labels `(i, j)` (left,
  right) is multiplied by `d_j` if `i = j` or `i → j` (i.e. `j = i + 1`), and fixed otherwise —
  exactly KL III's rule "`(-1)^{i_{α+1}}` if `i_α = i_{α+1}` or `i_α → i_{α+1}`".
* **Cups and caps** (`sigmaDatum_chi_cap`, `sigmaDatum_chi_cup`): the cap with outer region `λ`
  is multiplied by `d_i` if `λ_i ≡ 0 mod 4` and fixed otherwise; the cup with outer region `λ`
  by `d_i` if `λ_i ≡ 2 mod 4` and fixed otherwise, for both orientations. This is exactly the
  erratum's rule (p. 99: caps get `d_i^{λ_i - 1}` for `λ_i ∈ {2ℓ, 2ℓ+1, -2ℓ, -(2ℓ+3)}` resp.
  `{2ℓ, 2ℓ+1, -2ℓ, -(2ℓ+1)}`, cups for `λ_i ∈ {2ℓ+2, 2ℓ+3, -(2ℓ+1), -(2ℓ+2)}`, `ℓ ∈ 2ℤ_{≥0}`;
  on odd `λ_i` the factor `d_i^{λ_i - 1}` is `1`, and the even values listed are precisely
  `λ_i ≡ 0 mod 4`, resp. `≡ 2 mod 4`). The original KL III `Σ` fixed all cups and caps; then the
  degree-zero bubble with `λ_i - 1` dots is multiplied by `d_i^{λ_i - 1}`, which is `-1` for even
  `λ_i` and odd `d`-sign, contradicting "degree-zero bubbles are `1`" — this is what the erratum
  corrects. Our rescaling framework forces the clockwise bubble in the region `λ` to be multiplied
  by `a_i^{1 - λ_i}` (`RescaleDatum.weight_cwReal`); the erratum's cups and caps satisfy this
  (`sigmaDatum.cup_up`).
* **Downward crossings** (not specified by KL III or the erratum; the corresponding lines are
  commented out in the TeX source): they are forced by `Q`-cyclicity
  (`RescaleDatum.dnCross`): `F_j F_i 1_ν ⟶ F_i F_j 1_ν` is multiplied by
  `(d_j^{d_{ji}} c_{ij}^{-1}` for `i ≠ j`, `c_{ii}` for `i = j`) times the *weight-dependent*
  gauge factor `β(F_i, ν - j_X) β(F_j, ν) / (β(F_j, ν - i_X) β(F_i, ν))` coming from the
  erratum's cups, where `β(F_i, ρ) = d_i` if `ρ_i ≡ 0 mod 4` and `1` otherwise
  (`sigmaDatum_cup_dn`). So with the erratum's caps and cups the downward crossings are
  necessarily rescaled by weight-dependent signs; a weight-independent rule for them (as in the
  commented-out TeX) would not be compatible with `Q`-cyclicity.

With these generator scalars, `sigmaDatum.mapScalars kl` has the relations of `slnScalars`
(`sigmaDatum_mapScalars`): for `i ≠ j`, `t'_{ij} = d_i^{d_{ij}} (c_{ij} c_{ji})^{-1}`, which for
`j = i + 1` is `d_i d_j^{-1} = -1 = i - j` and `t'_{ji} = d_j d_j^{-1} = 1 = j - i`, and `1` for
non-adjacent `i, j`; `s' = 0`; `r'_i = (d_i c_{ii})^{-1} = d_i^{-2} = 1`. Equivalently the signed
scalars are *balanced* with the units `d_i` (`slnScalars_balanced`, see `equivOfBalanced`).

Since `sigmaEquiv` targets CL's `U_Q(sl_n)` (with `downCross = t_{ij}^{-1} rotCrossR`, and the
mixed relations `crossl ≫ crossr = t_{ji}`) and not the literal revised Definition 4.1 of the
erratum (which differs from CL's in the signs of the mixed relations for adjacent labels and
does not fix the downward crossing; see `Categorification.Diagrams.CL.Specialize`), this is not a
proof that the erratum's `Σ` is an isomorphism onto the erratum's `U→(sl_n)` as printed.

## Main results

* `Sln.sigmaDatum`, `Sln.sigmaDatum_mapScalars`;
* `Sln.sigmaEquiv : (presCL (slRootDatum m) k kl).Presented ≌ (presCL (slRootDatum m) k
  (slnScalars k m)).Presented` and `Sln.sigmaEquivPres` from KL III's `pres`.
-/

noncomputable section

namespace Categorification.KL3.Diagram.CL.Sln

open CategoryTheory StringDiagrams QuantumGroup UDot Presentation Flag Signed Rescale RescaleDatum

universe w

variable (k : Type w) [CommRing k] (m : ℕ)

local notation "SRD" => slRootDatum m

/-- KL's sign `d_i = (-1)^{i_KL}` for our vertex `i` (KL's vertex `i + 1`). -/
def sigmaSign (i : Fin m) : kˣ := (-1) ^ ((i : ℕ) + 1)

variable {k m}

theorem sigmaSign_mul_self (i : Fin m) : sigmaSign k m i * sigmaSign k m i = 1 := by
  rw [sigmaSign, ← mul_pow, neg_one_mul, neg_neg, one_pow]

theorem sigmaSign_inv (i : Fin m) : (sigmaSign k m i)⁻¹ = sigmaSign k m i :=
  inv_eq_of_mul_eq_one_right (sigmaSign_mul_self i)

theorem sigmaSign_succ {i j : Fin m} (h : (j : ℕ) = (i : ℕ) + 1) :
    sigmaSign k m j = -sigmaSign k m i := by
  rw [sigmaSign, sigmaSign, h, pow_succ, mul_neg_one]

/-- For `ε² = 1`, `ε^z` is `1` or `ε` according to the parity of `z`. -/
theorem zpow_of_mul_self_eq_one {G : Type*} [Group G] (ε : G) (hε : ε * ε = 1) (z : ℤ) :
    ε ^ z = if z % 2 = 0 then 1 else ε := by
  have h2 : ε ^ (2 : ℤ) = 1 := by rw [zpow_two, hε]
  conv_lhs => rw [← Int.emod_add_ediv z 2, zpow_add, zpow_mul, h2, one_zpow, mul_one]
  rcases Int.emod_two_eq_zero_or_one z with h | h
  · rw [h, zpow_zero, if_pos rfl]
  · rw [h, zpow_one, if_neg (by omega)]

variable (k m)

/-- **The rescaling datum of `Σ`** (KL III §4.2.1 with the erratum's cups and caps; see the
module docstring): dots `d_i`, upward crossings `d_j` if `i = j` or `j = i + 1`, cups and caps of
a strand labelled `i` whose right region `ρ` has `ρ_i ≡ 0 mod 4` get `d_i`. -/
def sigmaDatum : RescaleDatum SRD k where
  dot := sigmaSign k m
  cross i j := if i = j ∨ (j : ℕ) = (i : ℕ) + 1 then sigmaSign k m j else 1
  cup c := if ip SRD c.l.2 c.r % 4 = 0 then sigmaSign k m c.l.2 else 1
  cup_up i x := by
    have e : ip SRD i (sh SRD (up i) + x) = 2 + ip SRD i x := by
      simp only [ip, pair_sh, sgn_true, A_self, one_mul]
    simp only [e]
    rw [zpow_of_mul_self_eq_one _ (sigmaSign_mul_self i)]
    have h1 := sigmaSign_mul_self (k := k) i
    split_ifs <;> first | omega | simp [h1]

variable {k m}

@[simp] theorem sigmaDatum_dot (i : Fin m) : (sigmaDatum k m).dot i = sigmaSign k m i := rfl

@[simp] theorem sigmaDatum_cross (i j : Fin m) :
    (sigmaDatum k m).cross i j =
      if i = j ∨ (j : ℕ) = (i : ℕ) + 1 then sigmaSign k m j else 1 := rfl

/-- The erratum's cups `1_{λ} → F E` or `1_λ → E F` with outer region `λ` (library: the cup of
the colour `c`, outer region `sh c.l + c.r`): multiplied by `d_i` iff `λ_i ≡ 2 mod 4`. -/
theorem sigmaDatum_chi_cup (c : Col (Fin m) (Fin m → ℤ)) :
    (sigmaDatum k m).chi (.cup c) =
      if ip SRD c.l.2 (sh SRD c.l + c.r) % 4 = 2 then sigmaSign k m c.l.2 else 1 := by
  show (if ip SRD c.l.2 c.r % 4 = 0 then sigmaSign k m c.l.2 else 1) = _
  have e : ip SRD c.l.2 (sh SRD c.l + c.r) = sgn c.l.1 * 2 + ip SRD c.l.2 c.r := by
    simp only [ip, pair_sh, A_self]
  rw [e]
  have hs : sgn c.l.1 = 1 ∨ sgn c.l.1 = -1 := by cases c.l.1 <;> simp
  rcases hs with hs | hs <;> rw [hs] <;> split_ifs <;> first | rfl | omega

/-- The erratum's caps with outer region `λ` (library: the cap of the colour `c`, outer region
`c.r`): multiplied by `d_i` iff `λ_i ≡ 0 mod 4`. -/
theorem sigmaDatum_chi_cap (c : Col (Fin m) (Fin m → ℤ)) :
    (sigmaDatum k m).chi (.cap c) =
      if ip SRD c.l.2 c.r % 4 = 0 then sigmaSign k m c.l.2 else 1 := by
  show (if ip SRD c.l.2 c.r % 4 = 0 then sigmaSign k m c.l.2 else 1)⁻¹ = _
  split_ifs
  · exact sigmaSign_inv _
  · exact inv_one

/-- The gauge `β(F_i, ρ)` of the downward strands (entering the downward crossings). -/
theorem sigmaDatum_cup_dn (i : Fin m) (ρ : Fin m → ℤ) :
    (sigmaDatum k m).cup ⟨dn i, ρ⟩ = if ip SRD i ρ % 4 = 0 then sigmaSign k m i else 1 := rfl

/-- **`Σ` sends the KL scalars to the signed `sl_n` scalars** (up to the unused diagonal values
of `s`, which vanish on both sides): `t'_{ij} = i - j` for adjacent `i, j`, `t'_{ij} = 1`
otherwise, `s' = 0`, `r' = 1`. -/
theorem sigmaDatum_mapScalars :
    presCL SRD k ((sigmaDatum k m).mapScalars CLScalars.kl) = presCL SRD k (slnScalars k m) := by
  refine presCL_congr (fun i j h => ?_) (fun i j p q h => ?_) (funext fun i => ?_)
  · rw [mapScalars_t_of_ne _ _ h, slnScalars_t]
    simp only [CLScalars.kl_t, one_mul, sigmaDatum_dot, sigmaDatum_cross]
    have hji : ¬ j = i := Ne.symm h
    by_cases hadj : (slCartan m).dot i j = -1
    · rw [dij_of_adj hadj, pow_one]
      have h1 : (j : ℕ) = (i : ℕ) + 1 ∨ (i : ℕ) = (j : ℕ) + 1 := by
        have hh := hadj
        rw [slCartan_dot, if_neg h] at hh
        split_ifs at hh with h1; omega
      rcases h1 with h1 | h1
      · rw [if_pos (Or.inr h1), if_neg (by rintro (e | e); exacts [hji e, by omega]),
          sigmaSign_succ h1, mul_one, inv_neg, sigmaSign_inv, mul_neg, sigmaSign_mul_self]
        refine Units.ext ?_
        rw [slnT_of_adj k hadj, Units.val_neg, Units.val_one]
        push_cast [h1]
        ring
      · rw [if_neg (by rintro (e | e); exacts [h e, by omega]), if_pos (Or.inr h1),
          sigmaSign_succ h1, one_mul, inv_neg, sigmaSign_inv, mul_neg, neg_mul,
          sigmaSign_mul_self, neg_neg]
        refine Units.ext ?_
        rw [slnT_of_adj k hadj, Units.val_one]
        push_cast [h1]
        ring
    · have hn : ¬((i : ℕ) + 1 = (j : ℕ) ∨ (j : ℕ) + 1 = (i : ℕ)) := fun e =>
        hadj (by rw [slCartan_dot, if_neg h, if_pos e])
      have h0 : (slCartan m).dot i j = 0 := by rw [slCartan_dot, if_neg h, if_neg hn]
      rw [slnT_of_not_adj k hadj, (CartanDatum.dij_eq_zero_iff _ h).2 h0, pow_zero,
        if_neg (by rintro (e | e); exacts [h e, by omega]),
        if_neg (by rintro (e | e); exacts [hji e, by omega]), one_mul, one_mul, inv_one]
  · simp
  · simp only [mapScalars_r, CLScalars.kl_r, one_mul, sigmaDatum_dot, sigmaDatum_cross,
      true_or, if_true, slnScalars_r, sigmaSign_mul_self, inv_one]

variable (k m)

/-- **The isomorphism `Σ : U(sl_n) ≅ U_Q(sl_n)`** (KL III §4.2.1 with the erratum's cups and
caps): the rescaling by `sigmaDatum`, from `U_{kl}(sl_n)` (= KL III's `U(sl_n)`, `presCL_kl`) to
CL's `U_Q(sl_n)` with `t_{ij} = i - j` for adjacent `i, j`. It is `k`-linear, commutes with
whiskering and preserves degrees (`RescaleDatum.equiv_functor_whisk`,
`RescaleDatum.equiv_functor_homDeg`), and it is an isomorphism of categories
(`RescaleDatum.equiv_functor_comp_inverse`, `RescaleDatum.equiv_inverse_comp_functor`). -/
def sigmaEquiv :
    (presCL SRD k CLScalars.kl).Presented ≌ (presCL SRD k (slnScalars k m)).Presented :=
  (sigmaDatum k m).equiv CLScalars.kl sigmaDatum_mapScalars

/-- `Σ` on a diagram: the diagram times the product of the scalars of its generators. -/
theorem sigmaEquiv_diag {a b : Obj (psig SRD)} (d : a ⟶ b) :
    (sigmaEquiv k m).functor.map ((presCL SRD k CLScalars.kl).diag d) =
      ((weight (sigmaDatum k m).chi (Diagram.layers d) : kˣ) : k) •
        (presCL SRD k (slnScalars k m)).diag d :=
  equiv_functor_diag _ _ _ d

/-- **`Σ` from KL III's `U(sl_n)`** (`pres`, Definition 3.1) to CL's `U_Q(sl_n)` with signed
scalars. -/
def sigmaEquivPres : (pres SRD k).Presented ≌ (presCL SRD k (slnScalars k m)).Presented :=
  (by rw [presCL_kl SRD k] : (pres SRD k).Presented ≌ (presCL SRD k CLScalars.kl).Presented).trans
    (sigmaEquiv k m)

/-- The balancing units for the `A_m` path: `Σ` exhibits the signed scalars as balanced
(`equivOfBalanced`, CL Remark (3)): `t_{ij} d_i^{d_{ij}} = t_{ji} d_j^{d_{ji}}` for `i ≠ j`. -/
theorem slnScalars_balanced (i j : Fin m) (h : i ≠ j) :
    (slnScalars k m).t i j * sigmaSign k m i ^ (slCartan m).dij i j =
      (slnScalars k m).t j i * sigmaSign k m j ^ (slCartan m).dij j i := by
  by_cases hadj : (slCartan m).dot i j = -1
  · have hadj' : (slCartan m).dot j i = -1 := by rwa [(slCartan m).symm]
    rw [slnScalars_t, slnScalars_t, dij_of_adj hadj, dij_of_adj hadj', pow_one, pow_one]
    have h1 : (j : ℕ) = (i : ℕ) + 1 ∨ (i : ℕ) = (j : ℕ) + 1 := by
      have hh := hadj
      rw [slCartan_dot, if_neg h] at hh
      split_ifs at hh with h1; omega
    refine Units.ext ?_
    simp only [Units.val_mul]
    rw [slnT_of_adj k hadj, slnT_of_adj k hadj']
    rcases h1 with h1 | h1
    · rw [sigmaSign_succ h1, Units.val_neg]; push_cast [h1]; ring
    · rw [sigmaSign_succ h1, Units.val_neg]; push_cast [h1]; ring
  · have hn : ¬((i : ℕ) + 1 = (j : ℕ) ∨ (j : ℕ) + 1 = (i : ℕ)) := fun e =>
      hadj (by rw [slCartan_dot, if_neg h, if_pos e])
    have h0 : (slCartan m).dot i j = 0 := by rw [slCartan_dot, if_neg h, if_neg hn]
    have h0' : (slCartan m).dot j i = 0 := by rwa [(slCartan m).symm]
    rw [slnScalars_t, slnScalars_t, slnT_of_not_adj k hadj,
      slnT_of_not_adj k (not_adj_of_dot_eq_zero h0'), (CartanDatum.dij_eq_zero_iff _ h).2 h0,
      (CartanDatum.dij_eq_zero_iff _ (Ne.symm h)).2 h0', pow_zero, pow_zero]

end Categorification.KL3.Diagram.CL.Sln
