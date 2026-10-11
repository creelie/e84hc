import Mathlib

/-!
# The Fermat varieties of degree 51: finite steps

Checks behind Subsection `ssec:degree51` of the paper. The class left by Aoki's reduction lives
at level 102.

* `alpha_level_one`, `alpha2_level_one`, `alpha_sum`, `beta_hodge`: the characters
  `α = (1, 7, 51, 60, 85)` and `α' = (91, 34, 26, 98, 57)` of level 102 are of level one
  (`|tα| ∈ {2, 3}` for every unit `t`), `|tα| + |tα'| = 5`, and their join `β` satisfies
  `∑ ⟨tβ_k⟩ = 5 · 102` for every unit `t`: it is a Hodge character of the Fermat eightfold.
* `beta_no_pair`: no two entries of `β` add up to `0` modulo 102.
* `nu17_beta`, `nu17_pairs`, `nu17_standard`: the order parity `ν₁₇` is `1` on `β` and `0` on
  the generators of Aoki's group `S₁₀₂`.
* `familyA_weights`, `familyA_degrees`, `familyB_weights`, `familyB_degrees`, and the two
  chart conditions: the exponent conditions of the block families of degrees 6 and 18.
-/

namespace FermatHodge.Degree51

/-- `∑ ⟨t a_k⟩`, the sum of the representatives in `[0, 102)` of the entries of `t a`. -/
def wsum (a : List ℕ) (t : ℕ) : ℕ := (a.map (fun x => t * x % 102)).sum

def alpha : List ℕ := [1, 7, 51, 60, 85]
def alpha2 : List ℕ := [91, 34, 26, 98, 57]
def beta : List ℕ := alpha ++ alpha2

theorem alpha_sums : alpha.sum = 2 * 102 ∧ alpha2.sum = 3 * 102 := by decide

theorem alpha_level_one :
    ∀ t < 102, Nat.gcd t 102 = 1 → wsum alpha t = 2 * 102 ∨ wsum alpha t = 3 * 102 := by
  decide

theorem alpha2_level_one :
    ∀ t < 102, Nat.gcd t 102 = 1 → wsum alpha2 t = 2 * 102 ∨ wsum alpha2 t = 3 * 102 := by
  decide

theorem alpha_sum : ∀ t < 102, Nat.gcd t 102 = 1 → wsum alpha t + wsum alpha2 t = 5 * 102 := by
  decide

theorem beta_hodge : ∀ t < 102, Nat.gcd t 102 = 1 → wsum beta t = 5 * 102 := by
  decide

/-- `5 α = (5, 35, 51, 96, 17)`, the character of the second family, with `|5 α| = 2`. -/
theorem alpha_twist : alpha.map (fun x => 5 * x % 102) = [5, 35, 51, 96, 17] := by decide

theorem alpha_twisted_norm : wsum alpha 5 = 2 * 102 := by decide

/-- `37 α' = (1, 34, 44, 56, 69)`, the character of the first family, with `|37 α'| = 2`. -/
theorem alpha2_twist : alpha2.map (fun x => 37 * x % 102) = [1, 34, 44, 56, 69] := by decide

theorem alpha2_twisted_norm : wsum alpha2 37 = 2 * 102 := by decide

theorem beta_nonzero : ∀ y ∈ beta, y % 102 ≠ 0 := by decide

theorem beta_no_pair :
    ∀ i < 10, ∀ j < 10, i ≠ j → (beta.getD i 0 + beta.getD j 0) % 102 ≠ 0 := by
  decide

/-- The additive order of `y` in `ℤ/102`. -/
def ord (y : ℕ) : ℕ := 102 / Nat.gcd y 102

/-- The number of entries of order 17. -/
def n17 (a : List ℕ) : ℕ := (a.filter (fun y => ord y = 17)).length

theorem nu17_beta : beta.filter (fun y => ord y = 17) = [60] := by decide

theorem nu17_pairs : ∀ y < 102, 0 < y → n17 [y, 102 - y] % 2 = 0 := by decide

/-- Aoki's standard characters of level 102: `σ_{2,i} = (i, i + 51, -2i, 51)` for `0 < i < 51`,
`σ_{3,i} = (i, i + 34, i + 68, -3i)` for `0 < i < 34` and
`σ_{17,i} = (i, i + 6, …, i + 96, -17 i)` for `0 < i < 6`. -/
def std (p i : ℕ) : List ℕ :=
  if p = 2 then [i, i + 51, (204 - 2 * i) % 102, 51]
  else (List.range p).map (fun j => i + j * (102 / p)) ++ [(102 * p - p * i) % 102]

theorem nu17_standard :
    ∀ p ∈ [2, 3, 17], ∀ i < 102 / p, 0 < i → n17 (std p i) % 2 = 0 := by decide

/-! The standard characters are balanced; one statement per prime, as deciding all three at
once needs a deeper recursion than Lean's default. -/

set_option maxRecDepth 100000 in
theorem std_balanced_two :
    ∀ i < 51, 0 < i → ∀ t < 102, Nat.gcd t 102 = 1 → 2 * wsum (std 2 i) t = 4 * 102 := by
  decide

set_option maxRecDepth 100000 in
theorem std_balanced_three :
    ∀ i < 34, 0 < i → ∀ t < 102, Nat.gcd t 102 = 1 → 2 * wsum (std 3 i) t = 4 * 102 := by
  decide

set_option maxRecDepth 100000 in
theorem std_balanced_seventeen :
    ∀ i < 6, 0 < i → ∀ t < 102, Nat.gcd t 102 = 1 → 2 * wsum (std 17 i) t = 18 * 102 := by
  decide

/-! Exponent conditions.  A block is a list of five exponents and a degree; its weight is
`∑ α_k e_k`. -/

def weight (a e : List ℕ) : ℕ := (List.zipWith (· * ·) a e).sum

def degs (bl : List (List ℕ × ℕ)) : List ℕ :=
  (List.range 5).map (fun k => bl.foldl (fun acc e => acc + e.1.getD k 0 * e.2) 0)

/-- Family A, for `37 α' = (1, 34, 44, 56, 69)`: blocks `s, t, Q, F` of degrees `1, 1, 2, 3`,
with `u₀ = F²`, `u₁ = c₁ Q³`, `u₂ = c₂ t³ F`, `u₃ = c₃ s³ F`, `u₄ = c₄ s² t⁴`. -/
def blocksA : List (List ℕ × ℕ) :=
  [([0, 0, 0, 3, 2], 1), ([0, 0, 3, 0, 4], 1), ([0, 3, 0, 0, 0], 2), ([2, 0, 1, 1, 0], 3)]

theorem familyA_weights :
    blocksA.map (fun e => weight [1, 34, 44, 56, 69] e.1) = [306, 408, 102, 102] := by decide

theorem familyA_degrees : degs blocksA = [6, 6, 6, 6, 6] := by decide

/-- `A = ∏ B_l^{w_l / 102}` has degree `2D = 12`. -/
theorem familyA_A_degree :
    (blocksA.map (fun e => weight [1, 34, 44, 56, 69] e.1 / 102 * e.2)).sum = 12 := by
  decide

/-- The chart `(0, 4)`: no block occurs in both `u₀` and `u₄`. -/
theorem familyA_chart : blocksA.all (fun e => e.1.getD 0 0 * e.1.getD 4 0 = 0) = true := by
  decide

/-- Family B, for `5 α = (5, 35, 51, 96, 17)`: blocks `Q, t, F, s, G` of degrees
`2, 1, 9, 1, 6`, with `u₀ = G³`, `u₁ = c₁ s⁶ G²`, `u₂ = c₂ F²`, `u₃ = c₃ s t¹⁷`,
`u₄ = c₄ Q⁶ G`. -/
def blocksB : List (List ℕ × ℕ) :=
  [([0, 0, 0, 0, 6], 2), ([0, 0, 0, 17, 0], 1), ([0, 0, 2, 0, 0], 9), ([0, 6, 0, 1, 0], 1),
    ([3, 2, 0, 0, 1], 6)]

theorem familyB_weights :
    blocksB.map (fun e => weight [5, 35, 51, 96, 17] e.1) = [102, 1632, 102, 306, 102] := by
  decide

theorem familyB_degrees : degs blocksB = [18, 18, 18, 18, 18] := by decide

theorem familyB_A_degree :
    (blocksB.map (fun e => weight [5, 35, 51, 96, 17] e.1 / 102 * e.2)).sum = 36 := by
  decide

/-- The chart `(2, 3)`: no block occurs in both `u₂` and `u₃`. -/
theorem familyB_chart : blocksB.all (fun e => e.1.getD 2 0 * e.1.getD 3 0 = 0) = true := by
  decide

end FermatHodge.Degree51
