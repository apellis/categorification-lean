# Graded Grothendieck group and Euler form

## Source

Webster, arXiv:1309.3796v2. `K₀(T^λ)` is the Grothendieck group of finitely generated graded
projective `T^λ`-modules, a `ℤ[q, q⁻¹]`-module with `q` acting by grading shift; the
projectives `P^κ_i = e(i, κ)T^λ` (Definition 4.34) are right modules. The Euler form on
`K₀` pairs `[P]` and `[P']` by the graded dimension of `Hom(P, P')` (Lemma 4.36 states
`dim_q Hom(P^κ_i, P^{κ'}_{i'}) = ⟨p^κ_i, p^{κ'}_{i'}⟩`; Theorem 4.38 says the canonical
isomorphism intertwines the form of §4.7 with this Euler form).

## Lean

- `Graded.GProj 𝒜` (`Categorification/Algebra/Graded/K0.lean`): finitely generated graded
  projective LEFT modules over a graded algebra `A` with grading `𝒜`.
- `GProj.shift P a`: `(P{a})_d = P_{d−a}`.
- `Graded.K0 𝒜`: free abelian group on isomorphism classes of `GProj 𝒜`, modulo
  `[P ⊕ Q] = [P] + [Q]`; `ℤ[q, q⁻¹]` acts by `q^a [P] = [P{a}]`.
- `Graded.oppositeGrade 𝒜` (`RightTwist.lean`): the same grading on `Aᵐᵒᵖ`. Right graded
  `A`-modules are left graded `Aᵐᵒᵖ`-modules, so `K0 (oppositeGrade 𝒜)` is `K₀` of right
  graded projectives.
- `GProj.rightTwist ψ`, `K0.rightTwistEquiv ψ`: turn a left projective into a right one using
  a graded anti-involution `ψ`; preserve the Euler form (`homForm_rightTwistEquiv`).
- `K0.homForm 𝒜 x y` (`HomForm.lean`): biadditive, `homForm [P] [Q] = gdim HOM(P, Q)` as a
  Laurent series in `q`; `(q^a x, y) = q^{−a}(x, y)` (`homForm_T_smul_left`).

## Correspondence

| Source | Lean |
|---|---|
| `K₀(T^λ)` of graded right projectives, all weights | `⨁_β K0 (oppositeGrade (tensorProductGrade G β))` (`rightTensorProjectiveGroup`) |
| `q` acts by grading shift | `LaurentPolynomial ℤ`-module structure of `K0`; `T a` acts by `shift a` |
| Euler form `dim_q Hom(P, P')` | `homForm (oppositeGrade …) [P] [P']`, valued in `ℤ((q))` |

## Conventions

- Shift direction: `(M{a})_d = M_{d−a}`, so `q[P] = [P{1}]` lives one degree higher. Under the
  isomorphism of Theorem 4.38, this `q` goes to `v⁻¹` (`η` is semilinear for `q ↦ q⁻¹`,
  `inversion` in the spec file). Webster (§1, p. 6 of the arXiv PDF) sets `[A(i)] = qⁱ[A]`
  with `A(i)_n = A_{i+n}`, so his `q` lowers degrees: the library's `q` is Webster's `q⁻¹`.
- `gdim HOM(P, Q)` is a Laurent series in `q` with integer coefficients; the spec compares it
  with the rational form value through `lsCast` (integer to rational coefficients) and
  `algebraMap (RatFunc ℚ) (LaurentSeries ℚ)` (expansion of a rational function in the variable
  `X = v`).

## Sanity checks

- `Graded.K0.homForm_of`, `homForm_T_smul_left`, `homForm_rightTwistEquiv` (library lemmas).
- `scripts/NonVacuity.lean`: the Thm. 4.38 examples evaluate the Euler-form clause at concrete
  data.
