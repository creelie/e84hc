import Mathlib

/-!
# The Fermat varieties of degree 114: finite and algebraic steps

Checks behind Section `sec:fermat114` of the paper.

* `beta_hodge`, `alpha1_level_one`, `alpha2_level_one`, `alpha_sum`: the characters
  `α₁ = (1, 25, 43, 57, 102)` and `α₂ = (39, 63, 68, 80, 92)` of level 114 are of level one
  (`|tα| ∈ {2, 3}` for every unit `t`), `|tα₁| + |tα₂| = 5`, and their join `β` satisfies
  `∑ ⟨tβ_k⟩ = 5 · 114` for every unit `t`: it is a Hodge character of the Fermat eightfold.
* `beta_no_pair`: no two entries of `β` add up to `0` modulo 114.
* `nu19_beta`, `nu19_pairs`, `nu19_standard`: the order parity `ν₁₉` is `1` on `β` and `0` on
  the generators of Aoki's group `S₁₁₄`.
* `family1_sum`, `family1_res0`, `family1_res1`, `family1_residue`, `family1_at_two`: the five
  binary forms of family I add up to zero, and the residue computation of
  Proposition `prop:family1`.
* `family1_weights`, `family2_weights`, `family2_degrees`: the exponent conditions of the two
  families.
-/

namespace FermatHodge.Degree114

/-- `∑ ⟨t a_k⟩`, the sum of the representatives in `[0, 114)` of the entries of `t a`. -/
def wsum (a : List ℕ) (t : ℕ) : ℕ := (a.map (fun x => t * x % 114)).sum

def alpha1 : List ℕ := [1, 25, 43, 57, 102]
def alpha2 : List ℕ := [39, 63, 68, 80, 92]
def beta : List ℕ := alpha1 ++ alpha2

theorem alpha1_level_one :
    ∀ t < 114, Nat.gcd t 114 = 1 → wsum alpha1 t = 2 * 114 ∨ wsum alpha1 t = 3 * 114 := by
  decide

theorem alpha2_level_one :
    ∀ t < 114, Nat.gcd t 114 = 1 → wsum alpha2 t = 2 * 114 ∨ wsum alpha2 t = 3 * 114 := by
  decide

theorem alpha_sum : ∀ t < 114, Nat.gcd t 114 = 1 → wsum alpha1 t + wsum alpha2 t = 5 * 114 := by
  decide

theorem beta_hodge : ∀ t < 114, Nat.gcd t 114 = 1 → wsum beta t = 5 * 114 := by
  decide

theorem alpha1_norm : wsum alpha1 1 = 2 * 114 := by decide
theorem alpha2_twisted_norm : wsum alpha2 13 = 2 * 114 := by decide

theorem beta_no_pair : ∀ i < 10, ∀ j < 10, i ≠ j → (beta.getD i 0 + beta.getD j 0) % 114 ≠ 0 := by
  decide

/-- The additive order of `y` in `ℤ/114`. -/
def ord (y : ℕ) : ℕ := 114 / Nat.gcd y 114

/-- The number of entries of order 19. -/
def n19 (a : List ℕ) : ℕ := (a.filter (fun y => ord y = 19)).length

theorem nu19_beta : beta.filter (fun y => ord y = 19) = [102] := by decide

theorem nu19_pairs : ∀ y < 114, 0 < y → n19 [y, 114 - y] % 2 = 0 := by decide

/-- Aoki's standard characters of level 114: `σ_{2,i} = (i, i + 57, -2i, 57)` and, for
`p ∈ {3, 19}` and `d = 114 / p`, `σ_{p,i} = (i, i + d, …, i + (p-1)d, -p i)`. -/
def std (p i : ℕ) : List ℕ :=
  if p = 2 then [i, i + 57, (228 - 2 * i) % 114, 57]
  else (List.range p).map (fun j => i + j * (114 / p)) ++ [(114 * p - p * i) % 114]

theorem nu19_standard :
    ∀ p ∈ [2, 3, 19], ∀ i < 114 / p, 0 < i → n19 (std p i) % 2 = 0 := by decide

theorem std_sum : ∀ p ∈ [2, 3, 19], ∀ i < 114 / p, 0 < i → (std p i).sum % 114 = 0 := by
  decide

/-! Family I.  With `q = λ³ - 3λ² + 1`, in the chart `t = 1`. -/

theorem family1_sum (l s : ℚ) :
    (l ^ 3 - 3 * l ^ 2 + 1) * (s - l) + (-(l - 1) * (s - l) ^ 3) + (l - 1) * s * (s - 1) ^ 2
      + (-(l - 1) * (3 * l - 2) * s ^ 2) + l * (2 * l ^ 2 - 1) * (s - 1) = 0 := by
  ring

/-- The residue at `s = 0` is `-2 (u̇₄/u₄ - u̇₁/u₁)(0) / ((λ-1) q)`, with
`u̇₁/u₁ = 1/(λ-1) - 3/(s-λ)` and `u̇₄/u₄ = (6λ² - 1)/(λ(2λ² - 1))`.  Over the common
denominator `λ(λ-1)(2λ² - 1)` the bracket has numerator `-(2λ³ - 3λ + 2)`: -/
theorem family1_res0 (l : ℚ) :
    (6 * l ^ 2 - 1) * (l - 1) - l * (2 * l ^ 2 - 1) - 3 * (l - 1) * (2 * l ^ 2 - 1)
      = -(2 * l ^ 3 - 3 * l + 2) := by
  ring

/-- The residue at `s = 1` is `(u̇₃/u₃ - u̇₁/u₁)(1) / ((λ-1) q)`, with
`u̇₃/u₃ = 1/(λ-1) + 3/(3λ-2)` and `u̇₁/u₁(1) = 4/(λ-1)`; over `(3λ-2)(λ-1)` the bracket has
numerator `3(1 - 2λ)`: -/
theorem family1_res1 (l : ℚ) :
    (3 * l - 2) + 3 * (l - 1) - 4 * (3 * l - 2) = 3 * (1 - 2 * l) := by
  ring

/-- The sum of the two residues, over the common denominator
`λ(λ-1)²(3λ-2)(2λ²-1)q`: -/
theorem family1_residue (l : ℚ) :
    2 * (2 * l ^ 3 - 3 * l + 2) * (3 * l - 2) + 3 * (1 - 2 * l) * l * (2 * l ^ 2 - 1)
      = -(2 * l ^ 3 + 12 * l ^ 2 - 21 * l + 8) := by
  ring

theorem family1_at_two :
    -(2 * (2:ℚ) ^ 3 + 12 * 2 ^ 2 - 21 * 2 + 8)
        / (2 * (2 - 1) ^ 2 * (3 * 2 - 2) * (2 * 2 ^ 2 - 1) * (2 ^ 3 - 3 * 2 ^ 2 + 1)) = 5 / 28 := by
  norm_num

/-! Exponent conditions.  A block is a list of five exponents; its weight is `∑ α_k e_k`. -/

def weight (a e : List ℕ) : ℕ := (List.zipWith (· * ·) a e).sum

/-- Family I uses `13 α₂ = (51, 21, 86, 14, 56)`; blocks at `s = 0, 1, λ, ∞`. -/
theorem family1_weights :
    [[0, 0, 1, 2, 0], [0, 0, 2, 0, 1], [1, 3, 0, 0, 0], [2, 0, 0, 1, 2]].map
      (fun e => weight [51, 21, 86, 14, 56] e % 114) = [0, 0, 0, 0] := by decide

theorem alpha2_twist : alpha2.map (fun x => 13 * x % 114) = [51, 21, 86, 14, 56] := by decide

/-- Family II uses `α₁`; blocks `F, H, G, K, t` of degrees `7, 2, 12, 3, 1`. -/
theorem family2_weights :
    [[3, 1, 2, 0, 0], [0, 1, 5, 0, 1], [0, 0, 0, 2, 0], [1, 5, 0, 0, 1], [0, 0, 0, 0, 19]].map
      (fun e => weight alpha1 e) = [114, 342, 114, 228, 1938] := by decide

theorem family2_degrees :
    (List.range 5).map (fun k =>
      [([3, 1, 2, 0, 0], 7), ([0, 1, 5, 0, 1], 2), ([0, 0, 0, 2, 0], 12), ([1, 5, 0, 0, 1], 3),
        ([0, 0, 0, 0, 19], 1)].foldl (fun acc (e : List ℕ × ℕ) => acc + e.1.getD k 0 * e.2) 0)
      = [24, 24, 24, 24, 24] := by decide

end FermatHodge.Degree114
