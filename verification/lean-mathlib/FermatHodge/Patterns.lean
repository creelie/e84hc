import Mathlib

/-!
# Block patterns, and the elements of square one modulo 33 and 39

Checks behind `cor:patterns`, `lem:nusqrt` and the degrees `33` and `39` in the proof of
Theorem A.

* `patterns`: each of the seven rows of the table of `cor:patterns` is a block pattern
  (`def:blockpattern`): the column sums `∑_l δ_l e_{kl}` are all equal to `D` (P1), every
  column has a positive and a zero entry and a weight `e_l · ᾱ` divisible by `m` (P2), and
  `∑_l δ_l > D` (P3).
* `characters`: each `ᾱ` has entries in `[1, m)` adding up to `2m`; `multiples` identifies the
  rows with the characters of the paper.
* `roots33`, `roots39`, `nuR_O`, `nuR_standard`, `nuR_pairs`: the parity `ν_R` of the number of
  elements of square `1` is `1` on `O₃₃` and `O₃₉` and `0` on pairs and standard characters.
-/

namespace FermatHodge.Patterns

/-- `e · a = ∑_k a_k e_k`. -/
def weight (a e : List ℕ) : ℕ := (List.zipWith (· * ·) a e).sum

/-- The vector `(∑_l δ_l e_{kl})_k` of a list of columns `(e_l, δ_l)`. -/
def colSum (bl : List (List ℕ × ℕ)) : List ℕ :=
  (List.range 5).map (fun k => (bl.map (fun e => e.1.getD k 0 * e.2)).sum)

/-- Conditions (P1)–(P3) of a block pattern with constant `D` for `ᾱ = a` at level `m`. -/
def isPattern (m D : ℕ) (a : List ℕ) (bl : List (List ℕ × ℕ)) : Bool :=
  colSum bl == List.replicate 5 D &&
    bl.all (fun e => e.1.length == 5 && e.1.any (fun x => 0 < x) && e.1.any (fun x => x == 0) &&
      weight a e.1 % m == 0 && 0 < e.2) &&
    D < (bl.map Prod.snd).sum

/-- `ᾱ` has five entries in `[1, m)` adding up to `2m`. -/
def isCharacter (m : ℕ) (a : List ℕ) : Bool :=
  a.length == 5 && a.all (fun x => 0 < x && x < m) && a.sum == 2 * m

/-- The rows of the table of `cor:patterns`: `(m, D, ᾱ, columns)`. -/
def rows : List (ℕ × ℕ × List ℕ × List (List ℕ × ℕ)) :=
  [(114, 3, [51, 21, 86, 14, 56],
      [([0, 0, 1, 2, 0], 1), ([0, 0, 2, 0, 1], 1), ([1, 3, 0, 0, 0], 1), ([2, 0, 0, 1, 2], 1)]),
    (114, 24, [1, 25, 43, 57, 102],
      [([3, 1, 2, 0, 0], 7), ([0, 1, 5, 0, 1], 2), ([0, 0, 0, 2, 0], 12), ([1, 5, 0, 0, 1], 3),
        ([0, 0, 0, 0, 19], 1)]),
    (44, 11, [1, 5, 8, 33, 41],
      [([3, 0, 0, 0, 1], 1), ([0, 0, 11, 0, 0], 1), ([1, 1, 0, 0, 2], 5), ([1, 2, 0, 1, 0], 3),
        ([0, 0, 0, 4, 0], 2)]),
    (52, 14, [1, 5, 16, 37, 45],
      [([0, 0, 0, 3, 1], 4), ([0, 1, 1, 0, 3], 1), ([2, 1, 0, 0, 1], 7), ([0, 0, 13, 0, 0], 1),
        ([0, 3, 0, 1, 0], 2)]),
    (52, 5, [1, 6, 14, 34, 49],
      [([0, 0, 5, 1, 0], 1), ([3, 0, 0, 0, 1], 1), ([2, 0, 0, 3, 0], 1), ([0, 3, 0, 1, 0], 1),
        ([0, 1, 0, 0, 2], 2)]),
    (102, 6, [1, 34, 44, 56, 69],
      [([0, 0, 0, 3, 2], 1), ([0, 0, 3, 0, 4], 1), ([0, 3, 0, 0, 0], 2), ([2, 0, 1, 1, 0], 3)]),
    (102, 18, [5, 35, 51, 96, 17],
      [([0, 0, 0, 0, 6], 2), ([0, 0, 0, 17, 0], 1), ([0, 0, 2, 0, 0], 9), ([0, 6, 0, 1, 0], 1),
        ([3, 2, 0, 0, 1], 6)])]

theorem patterns : rows.all (fun r => isPattern r.1 r.2.1 r.2.2.1 r.2.2.2) = true := by decide

theorem characters : rows.all (fun r => isCharacter r.1 r.2.2.1) = true := by decide

theorem constants : rows.map (fun r => r.2.1) = [3, 24, 11, 14, 5, 6, 18] := by decide

/-- The degrees add up to `D + 1` in every row. -/
theorem degree_sums :
    rows.map (fun r => (r.2.2.2.map Prod.snd).sum) = [4, 25, 12, 15, 6, 7, 19] := by decide

/-- The rows are `13 α₂`, `α₁` (level 114), `α` (level 44), `α`, `9 α'` (level 52) and
`37 α'`, `5 α` (level 102), with the characters of `Degree114`, `Degree44`, `Degree52` and
`Degree51`. -/
theorem multiples :
    [39, 63, 68, 80, 92].map (fun x => 13 * x % 114) = [51, 21, 86, 14, 56] ∧
      [29, 18, 42, 50, 17].map (fun x => 9 * x % 52) = [1, 6, 14, 34, 49] ∧
      [91, 34, 26, 98, 57].map (fun x => 37 * x % 102) = [1, 34, 44, 56, 69] ∧
      [1, 7, 51, 60, 85].map (fun x => 5 * x % 102) = [5, 35, 51, 96, 17] := by
  decide

/-! The homomorphism `ν_R` of `lem:nusqrt` for `M = 33` and `M = 39`. -/

/-- The elements of `ℤ/M` with square `1`. -/
def roots (M : ℕ) : List ℕ := (List.range M).filter (fun y => y * y % M == 1)

/-- `ν_R(a)`: the parity of the number of entries of `a` with square `1`. -/
def nuR (M : ℕ) (a : List ℕ) : ℕ := (a.filter (fun y => y * y % M == 1)).length % 2

def O33 : List ℕ := [1, 4, 16, 22, 25, 31]
def O39 : List ℕ := [1, 7, 16, 22, 34, 37]

theorem roots33 : roots 33 = [1, 10, 23, 32] := by decide

theorem roots39 : roots 39 = [1, 14, 25, 38] := by decide

theorem O_roots : O33.filter (fun y => y * y % 33 == 1) = [1] ∧
    O39.filter (fun y => y * y % 39 == 1) = [1] := by
  decide

theorem nuR_O : nuR 33 O33 = 1 ∧ nuR 39 O39 = 1 := by decide

/-- `∑ ⟨t a_k⟩`, the sum of the representatives in `[0, M)` of the entries of `t a`. -/
def wsum (M : ℕ) (a : List ℕ) (t : ℕ) : ℕ := (a.map (fun x => t * x % M)).sum

/-- `O₃₃` and `O₃₉` are balanced: `∑ ⟨t a_k⟩ = 3M` for every unit `t`. -/
theorem O_balanced :
    (∀ t < 33, Nat.gcd t 33 = 1 → wsum 33 O33 t = 3 * 33) ∧
      (∀ t < 39, Nat.gcd t 39 = 1 → wsum 39 O39 t = 3 * 39) := by
  decide

/-- Aoki's standard characters of level `M`: for a prime `p ∣ M` and `d = M / p`,
`σ_{p,i} = (i, i + d, …, i + (p-1)d, -p i)`. -/
def std (M p i : ℕ) : List ℕ :=
  (List.range p).map (fun j => i + j * (M / p)) ++ [(M * p - p * i) % M]

theorem nuR_standard :
    (∀ p ∈ [3, 11], ∀ i < 33 / p, 0 < i → nuR 33 (std 33 p i) = 0) ∧
      (∀ p ∈ [3, 13], ∀ i < 39 / p, 0 < i → nuR 39 (std 39 p i) = 0) := by
  decide

theorem nuR_pairs :
    (∀ y < 33, 0 < y → nuR 33 [y, 33 - y] = 0) ∧ (∀ y < 39, 0 < y → nuR 39 [y, 39 - y] = 0) := by
  decide

end FermatHodge.Patterns
