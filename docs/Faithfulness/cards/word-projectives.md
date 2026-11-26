# Word projectives `P^κ_i` and their classes

## Source

Webster, arXiv:1309.3796v2, Definition 4.34: for a Stendhal triple `(i, λ, κ)` (black colours
`i`, red labels `λ`, `κ(m)` = number of black strands left of the `m`-th red strand), possibly
with divided powers in `i`, `P^κ_i = e(i, κ)T^λ`, a graded right projective `T^λ`-module.
With divided powers, `e(i, κ)` uses the nilHecke idempotent on each block of equal colours.
Theorem 4.38 maps `[P^κ_i]` to `p^κ_i`.

## Lean

- `Stendhal.TensorWord I n` (`TensorGenerators.lean`): words built by `empty`, `red w`
  (append a red strand, `n ↦ n + 1`) and `black w i a` (append a black block of colour `i`
  and multiplicity `a`, a divided power). `ℓ` counts the red strands; their labels come from
  the position.
- `tensorWordProjective Λ C hQ w` (`TensorWordProjectives.lean`): `dividedSequenceProj` of
  the expanded word: the left projective of the nilHecke idempotent pushed to `T^λ`, with the
  Cartan shift of the divided power retained.
- `rightTensorWordProjective C hQ Λ w` (`RightTensorHomForm.lean`): its right twist by the
  horizontal reflection anti-involution `tensorReflectionG` of `T^λ`.
- `rightTensorWordProjectiveClass C hQ Λ w`: its class in the black-content summand
  `w.content` of `⨁_β K₀`.
- `rightTensorProjectiveGroup C hQ Λ β = K0 (oppositeGrade (tensorProductGrade G β))`.

## Correspondence

| Source | Lean |
|---|---|
| sequence `i` of black colours, positions `κ` of red strands | `TensorWord`: the order of `red` and `black` constructors records both |
| divided powers in `i` | `black w i a` with multiplicity `a` |
| `e(i, κ)` | expanded red-ordered idempotent, times nilHecke idempotents on divided blocks |
| right module `e(i, κ)T^λ` | right twist of the left module `T^λ e(i, κ)` by horizontal reflection |
| `[P^κ_i] ∈ K₀(T^λ)` | `rightTensorWordProjectiveClass` |

## Conventions

- Horizontal reflection sends `T^λ e` to `e T^λ` (reflection reverses products), so the right
  twist of the left word projective is the right word projective.
- Divided-power shift: the divided projective is normalized so that the expanded projective
  has class `[a]! ·` its class (`tensorWordProjective_factorial`). Reviewers should compare the
  normalizing shift with Webster's convention for divided powers.
- Only black strands with downward orientation occur; double Stendhal triples with upward
  strands are not needed for `T^λ` (Definition 4.34 allows them, with `DT^λ e₋ = T^λ`).

## Sanity checks

- `scripts/NonVacuity.lean` (Thm. 4.38 examples).
