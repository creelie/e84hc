import Mathlib

/-!
# The Fermat varieties of degree 44: finite steps

Checks behind Subsection `ssec:degree44` of the paper.

* `alpha_level_one`, `types_complementary`, `beta_hodge`: the threefold character
  `α = (1, 5, 8, 33, 41)` and the curve character `b = (9, 37, 42)` of level 44 satisfy
  `|tα| ∈ {2, 3}` and `|tα| + |tb| = 4` for every unit `t`, so their join `β` satisfies
  `∑ ⟨tβ_k⟩ = 4 · 44`: it is a Hodge character of the Fermat sixfold.
* `beta_no_pair`: no two entries of `β` add up to `0` modulo 44.
* `nu11_beta`, `nu11_pairs`, `nu11_standard`: the order parity `ν₁₁` is `1` on `β` and `0` on
  the generators of Aoki's group `S₄₄`.
* `family_weights`, `family_degrees`: the exponent conditions of the block family of degree 11.
-/

namespace FermatHodge.Degree44

/-- `∑ ⟨t a_k⟩`, the sum of the representatives in `[0, 44)` of the entries of `t a`. -/
def wsum (a : List ℕ) (t : ℕ) : ℕ := (a.map (fun x => t * x % 44)).sum

def alpha : List ℕ := [1, 5, 8, 33, 41]
def b : List ℕ := [9, 37, 42]
def beta : List ℕ := alpha ++ b

theorem alpha_sum_zero : alpha.sum % 44 = 0 ∧ b.sum % 44 = 0 := by decide

theorem alpha_level_one :
    ∀ t < 44, Nat.gcd t 44 = 1 → wsum alpha t = 2 * 44 ∨ wsum alpha t = 3 * 44 := by
  decide

theorem types_complementary :
    ∀ t < 44, Nat.gcd t 44 = 1 → wsum alpha t + wsum b t = 4 * 44 := by
  decide

theorem beta_hodge : ∀ t < 44, Nat.gcd t 44 = 1 → wsum beta t = 4 * 44 := by
  decide

theorem alpha_norm : wsum alpha 1 = 2 * 44 := by decide

theorem beta_nonzero : ∀ y ∈ beta, y % 44 ≠ 0 := by decide

theorem beta_no_pair : ∀ i < 8, ∀ j < 8, i ≠ j → (beta.getD i 0 + beta.getD j 0) % 44 ≠ 0 := by
  decide

/-- The additive order of `y` in `ℤ/44`. -/
def ord (y : ℕ) : ℕ := 44 / Nat.gcd y 44

/-- The number of entries of order 11. -/
def n11 (a : List ℕ) : ℕ := (a.filter (fun y => ord y = 11)).length

theorem nu11_beta : beta.filter (fun y => ord y = 11) = [8] := by decide

theorem nu11_pairs : ∀ y < 44, 0 < y → n11 [y, 44 - y] % 2 = 0 := by decide

/-- Aoki's standard characters of level 44: `σ_{2,i} = (i, i + 22, -2i, 22)` for `0 < i < 22`
and `σ_{11,i} = (i, i + 4, …, i + 40, -11 i)` for `0 < i < 4`. -/
def std (p i : ℕ) : List ℕ :=
  if p = 2 then [i, i + 22, (88 - 2 * i) % 44, 22]
  else (List.range p).map (fun j => i + j * (44 / p)) ++ [(44 * p - p * i) % 44]

theorem nu11_standard :
    ∀ p ∈ [2, 11], ∀ i < 44 / p, 0 < i → n11 (std p i) % 2 = 0 := by decide

theorem std_balanced :
    ∀ p ∈ [2, 11], ∀ i < 44 / p, 0 < i → ∀ t < 44, Nat.gcd t 44 = 1 →
      2 * wsum (std p i) t = (std p i).length * 44 := by
  decide

/-! The block family: blocks `s, t, P, Q, S` of degrees `1, 1, 5, 3, 2`, with
`u₀ = c₀ s³ P Q`, `u₁ = c₁ P Q²`, `u₂ = t¹¹`, `u₃ = c₃ Q S⁴`, `u₄ = s P²`. -/

def weight (a e : List ℕ) : ℕ := (List.zipWith (· * ·) a e).sum

def blocks : List (List ℕ × ℕ) :=
  [([3, 0, 0, 0, 1], 1), ([0, 0, 11, 0, 0], 1), ([1, 1, 0, 0, 2], 5), ([1, 2, 0, 1, 0], 3),
    ([0, 0, 0, 4, 0], 2)]

theorem family_weights :
    blocks.map (fun e => weight alpha e.1) = [44, 88, 88, 44, 132] := by decide

theorem family_degrees :
    (List.range 5).map (fun k => blocks.foldl (fun acc e => acc + e.1.getD k 0 * e.2) 0)
      = [11, 11, 11, 11, 11] := by decide

/-- `A = ∏ B_l^{w_l / 44}` has degree `2D = 22`. -/
theorem family_A_degree :
    (blocks.map (fun e => weight alpha e.1 / 44 * e.2)).sum = 22 := by decide

/-- The chart `(0, 2)`: no block occurs in both `u₀` and `u₂`. -/
theorem family_chart : blocks.all (fun e => e.1.getD 0 0 * e.1.getD 2 0 = 0) = true := by decide

end FermatHodge.Degree44
