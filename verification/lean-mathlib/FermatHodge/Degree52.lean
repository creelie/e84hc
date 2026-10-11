import Mathlib

/-!
# The Fermat varieties of degree 52: finite steps

Checks behind Subsection `ssec:degree52` of the paper.

* `alpha_level_one`, `alpha2_level_one`, `alpha_sum`, `beta_hodge`: the characters
  `α = (1, 5, 16, 37, 45)` and `α' = (29, 18, 42, 50, 17)` of level 52 are of level one
  (`|tα| ∈ {2, 3}` for every unit `t`), `|tα| + |tα'| = 5`, and their join `β` satisfies
  `∑ ⟨tβ_k⟩ = 5 · 52` for every unit `t`: it is a Hodge character of the Fermat eightfold.
* `beta_no_pair`: no two entries of `β` add up to `0` modulo 52.
* `nu13_beta`, `nu13_pairs`, `nu13_standard`: the order parity `ν₁₃` is `1` on `β` and `0` on
  the generators of Aoki's group `S₅₂`.
* `familyA_weights`, `familyA_degrees`, `familyB_weights`, `familyB_degrees`, and the two
  chart conditions: the exponent conditions of the block families of degrees 14 and 5.
-/

namespace FermatHodge.Degree52

/-- `∑ ⟨t a_k⟩`, the sum of the representatives in `[0, 52)` of the entries of `t a`. -/
def wsum (a : List ℕ) (t : ℕ) : ℕ := (a.map (fun x => t * x % 52)).sum

def alpha : List ℕ := [1, 5, 16, 37, 45]
def alpha2 : List ℕ := [29, 18, 42, 50, 17]
def beta : List ℕ := alpha ++ alpha2

theorem alpha_sum_zero : alpha.sum % 52 = 0 ∧ alpha2.sum % 52 = 0 := by decide

theorem alpha_level_one :
    ∀ t < 52, Nat.gcd t 52 = 1 → wsum alpha t = 2 * 52 ∨ wsum alpha t = 3 * 52 := by
  decide

theorem alpha2_level_one :
    ∀ t < 52, Nat.gcd t 52 = 1 → wsum alpha2 t = 2 * 52 ∨ wsum alpha2 t = 3 * 52 := by
  decide

theorem alpha_sum : ∀ t < 52, Nat.gcd t 52 = 1 → wsum alpha t + wsum alpha2 t = 5 * 52 := by
  decide

theorem beta_hodge : ∀ t < 52, Nat.gcd t 52 = 1 → wsum beta t = 5 * 52 := by
  decide

theorem alpha_norm : wsum alpha 1 = 2 * 52 := by decide

/-- `9 α' = (1, 6, 14, 34, 49)`, the character of the second family, with `|9 α'| = 2`. -/
theorem alpha2_twist : alpha2.map (fun x => 9 * x % 52) = [1, 6, 14, 34, 49] := by decide

theorem alpha2_twisted_norm : wsum alpha2 9 = 2 * 52 := by decide

theorem beta_nonzero : ∀ y ∈ beta, y % 52 ≠ 0 := by decide

theorem beta_no_pair :
    ∀ i < 10, ∀ j < 10, i ≠ j → (beta.getD i 0 + beta.getD j 0) % 52 ≠ 0 := by
  decide

/-- The additive order of `y` in `ℤ/52`. -/
def ord (y : ℕ) : ℕ := 52 / Nat.gcd y 52

/-- The number of entries of order 13. -/
def n13 (a : List ℕ) : ℕ := (a.filter (fun y => ord y = 13)).length

theorem nu13_beta : beta.filter (fun y => ord y = 13) = [16] := by decide

theorem nu13_pairs : ∀ y < 52, 0 < y → n13 [y, 52 - y] % 2 = 0 := by decide

/-- Aoki's standard characters of level 52: `σ_{2,i} = (i, i + 26, -2i, 26)` for `0 < i < 26`
and `σ_{13,i} = (i, i + 4, …, i + 48, -13 i)` for `0 < i < 4`. -/
def std (p i : ℕ) : List ℕ :=
  if p = 2 then [i, i + 26, (104 - 2 * i) % 52, 26]
  else (List.range p).map (fun j => i + j * (52 / p)) ++ [(52 * p - p * i) % 52]

theorem nu13_standard :
    ∀ p ∈ [2, 13], ∀ i < 52 / p, 0 < i → n13 (std p i) % 2 = 0 := by decide

theorem std_balanced :
    ∀ p ∈ [2, 13], ∀ i < 52 / p, 0 < i → ∀ t < 52, Nat.gcd t 52 = 1 →
      2 * wsum (std p i) t = (std p i).length * 52 := by
  decide

/-! Exponent conditions.  A block is a list of five exponents and a degree; its weight is
`∑ α_k e_k`. -/

def weight (a e : List ℕ) : ℕ := (List.zipWith (· * ·) a e).sum

def degs (bl : List (List ℕ × ℕ)) : List ℕ :=
  (List.range 5).map (fun k => bl.foldl (fun acc e => acc + e.1.getD k 0 * e.2) 0)

/-- Family A, for `α`: blocks `G, s, F, t, H` of degrees `4, 1, 7, 1, 2`, with
`u₀ = c₀ F²`, `u₁ = c₁ s F H³`, `u₂ = s t¹³`, `u₃ = c₃ G³ H`, `u₄ = c₄ s³ G F`. -/
def blocksA : List (List ℕ × ℕ) :=
  [([0, 0, 0, 3, 1], 4), ([0, 1, 1, 0, 3], 1), ([2, 1, 0, 0, 1], 7), ([0, 0, 13, 0, 0], 1),
    ([0, 3, 0, 1, 0], 2)]

theorem familyA_weights :
    blocksA.map (fun e => weight alpha e.1) = [156, 156, 52, 208, 52] := by decide

theorem familyA_degrees : degs blocksA = [14, 14, 14, 14, 14] := by decide

/-- `A = ∏ B_l^{w_l / 52}` has degree `2D = 28`. -/
theorem familyA_A_degree : (blocksA.map (fun e => weight alpha e.1 / 52 * e.2)).sum = 28 := by
  decide

/-- The chart `(0, 2)`: no block occurs in both `u₀` and `u₂`. -/
theorem familyA_chart : blocksA.all (fun e => e.1.getD 0 0 * e.1.getD 2 0 = 0) = true := by
  decide

/-- Family B, for `9 α' = (1, 6, 14, 34, 49)`: blocks `t, s, s - t, L, Q` of degrees
`1, 1, 1, 1, 2`, with `u₀ = c₀ s³ (s-t)²`, `u₁ = c₁ L³ Q`, `u₂ = t⁵`, `u₃ = c₃ t (s-t)³ L`,
`u₄ = c₄ s Q²`. -/
def blocksB : List (List ℕ × ℕ) :=
  [([0, 0, 5, 1, 0], 1), ([3, 0, 0, 0, 1], 1), ([2, 0, 0, 3, 0], 1), ([0, 3, 0, 1, 0], 1),
    ([0, 1, 0, 0, 2], 2)]

theorem familyB_weights :
    blocksB.map (fun e => weight [1, 6, 14, 34, 49] e.1) = [104, 52, 104, 52, 104] := by decide

theorem familyB_degrees : degs blocksB = [5, 5, 5, 5, 5] := by decide

theorem familyB_A_degree :
    (blocksB.map (fun e => weight [1, 6, 14, 34, 49] e.1 / 52 * e.2)).sum = 10 := by
  decide

/-- The chart `(1, 2)`: no block occurs in both `u₁` and `u₂`. -/
theorem familyB_chart : blocksB.all (fun e => e.1.getD 1 0 * e.1.getD 2 0 = 0) = true := by
  decide

end FermatHodge.Degree52
