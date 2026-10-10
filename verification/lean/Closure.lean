/-
  Machine checks for "When is every rational Hodge class algebraic?"
  (paper/main.tex).  Lean 4 core only: no Mathlib, no `sorry`, no
  `native_decide`.  Nothing in the paper depends on this file; it re-checks
  the finite and purely logical steps.

  Part 1. The rule set of Table 1 and Theorem B: which sets of statements
          give the conjecture.
  Part 2. The counting lemma behind the switch lemma (Lemma 4.1).
  Part 3. The dimension counts for Weil families and Prym loci (Section 5).
  Part 4. Picard numbers of the Fermat quartic, quintic and sextic surfaces
          from the character formula (Section 3).
  Part 5. The three exceptional orbits of Fermat fourfolds of odd degree
          divisible by 3 (Section 3.7): they are balanced, contain no pair,
          generate, and have no direct or lowering move; and the identities
          that make them algebraic hold, with every part balanced.
-/

namespace Closure

/-! ## Part 1: the routes -/

/-- The statements of the rule set.  `F2` is the Hodge conjecture for abelian
varieties, `F3P` is (F3'), `L` the Lefschetz standard conjecture for every
variety, `M` "every Hodge class is motivated", `V` the variational Hodge
conjecture, `IP` propagation from CM points in abelian schemes, `CM` the
Hodge conjecture for abelian varieties of CM type, `SR` the semiregularity
of Schoen's subvariety, `W3` the Weil classes of the split families of
Q(sqrt -3), `FER` the Hodge conjecture for Fermat varieties. -/
inductive St
  | F2 | F3P | L | M | V | IP | CM | SR | HC | FER | W3
  deriving DecidableEq, Repr

open St

structure Rule where
  prem : List St
  concl : St
  deriving DecidableEq

/-- Every rule is proved or cited in the paper (Table 1 there). -/
def rules : List Rule :=
  [ ⟨[F2, F3P], HC⟩,                       -- Theorem A
    ⟨[HC], F2⟩, ⟨[HC], F3P⟩,                -- Lemma 2.11
    ⟨[HC], L⟩, ⟨[HC], M⟩, ⟨[HC], V⟩,         -- Lemma 2.11
    ⟨[L, M], HC⟩,                          -- Proposition 2.8
    ⟨[L], F2⟩,                             -- [Mil20, Theorem 4]
    ⟨[V], F2⟩,                             -- [Mil20, Theorem 3]
    ⟨[V], IP⟩,                             -- IP is a case of V
    ⟨[F3P], M⟩,                            -- Proposition 2.9
    ⟨[CM, IP], F2⟩,                        -- Proposition 4.4
    ⟨[F2], IP⟩, ⟨[F2], CM⟩,                 -- Proposition 4.4
    ⟨[CM], FER⟩, ⟨[HC], FER⟩,               -- Theorem C
    ⟨[SR], W3⟩,                            -- Cor 5.8; Thm 2.3, [Sch88, Sch98]
    ⟨[F2], W3⟩ ]                           -- W3 is a case of F2

/-- `Derivable S a`: the statement `a` follows from the statements in `S` by
the rules. -/
inductive Derivable (S : St → Prop) : St → Prop
  | base {a : St} : S a → Derivable S a
  | rule {r : Rule} : r ∈ rules → (∀ p ∈ r.prem, Derivable S p) →
      Derivable S r.concl

/-- A set closed under the rules, as a boolean test that `decide` can run. -/
def closedB (T : St → Bool) : Bool :=
  rules.all (fun r => !(r.prem.all T) || T r.concl)

theorem closed_of_closedB {T : St → Bool} (h : closedB T = true) :
    ∀ r ∈ rules, (∀ p ∈ r.prem, T p = true) → T r.concl = true := by
  intro r hr hp
  have h1 := (List.all_eq_true.mp h) r hr
  have h2 : r.prem.all T = true := List.all_eq_true.mpr hp
  simp only [h2, Bool.not_true, Bool.false_or] at h1
  exact h1

/-- Everything derivable from a subset of a closed set lies in that set. -/
theorem derivable_in_closed {S : St → Prop} {T : St → Bool}
    (hT : closedB T = true) (hS : ∀ a, S a → T a = true) :
    ∀ a, Derivable S a → T a = true := by
  intro a h
  induction h with
  | base h => exact hS _ h
  | rule hr _ ih => exact closed_of_closedB hT _ hr ih

/-- The closed set used for each obstruction: all statements but `out`. -/
def allBut (out : List St) : St → Bool := fun a => !(out.contains a)

/-- The four closed sets of the proof of Theorem B. -/
theorem closed_noHC_M_F3P : closedB (allBut [HC, M, F3P]) = true := by decide
theorem closed_noHC_L_F3P : closedB (allBut [HC, L, F3P]) = true := by decide
theorem closed_noHC_F2_L_V_IP : closedB (allBut [HC, F2, L, V, IP]) = true := by
  decide
theorem closed_noHC_F2_L_V_CM : closedB (allBut [HC, F2, L, V, CM]) = true := by
  decide

/-- What (CM) gives: exactly itself and the Fermat varieties. -/
def cmClosure : St → Bool := fun a => a == CM || a == FER

theorem closed_cm : closedB cmClosure = true := by decide

/-- (CM) and every rule hold, and the Hodge conjecture fails: nothing proved
in the paper, together with (CM), gives the conjecture. -/
theorem countermodel : ¬ Derivable (fun a => a = CM) HC := by
  intro h
  have := derivable_in_closed closed_cm (fun a ha => by subst ha; rfl) HC h
  exact absurd this (by decide)

/-- Schoen's question, with (CM), does not give the conjecture. -/
theorem schoen_alone : ¬ Derivable (fun a => a = SR ∨ a = CM) HC := by
  intro h
  have := derivable_in_closed closed_noHC_F2_L_V_IP
    (fun a ha => by rcases ha with rfl | rfl <;> rfl) HC h
  exact absurd this (by decide)

private theorem out_of {S : St → Prop} {out : List St}
    (hT : closedB (allBut out) = true) (hS : ∀ a, S a → ¬ a ∈ out) :
    Derivable S HC → HC ∈ out → False := by
  intro h hHC
  have := derivable_in_closed hT (fun a ha => by
    have := hS a ha
    simp [allBut, this]) HC h
  simp [allBut, hHC] at this

/-- **Theorem B.**  If a set `S` of statements, not containing the
conjecture, gives the conjecture, then either `S` contains (F3') together
with F2, L, V or both CM and IP, or `S` contains both L and M. -/
theorem routes (S : St → Prop) (hHC : ¬ S HC) (h : Derivable S HC) :
    (S F3P ∧ (S F2 ∨ S L ∨ S V ∨ (S CM ∧ S IP))) ∨ (S L ∧ S M) := by
  apply Classical.byContradiction
  intro hno
  have h1 : ¬ (S F3P ∧ (S F2 ∨ S L ∨ S V ∨ (S CM ∧ S IP))) :=
    fun hx => hno (Or.inl hx)
  have h2 : ¬ (S L ∧ S M) := fun hx => hno (Or.inr hx)
  by_cases hF : S F3P
  · have hF2 : ¬ S F2 := fun x => h1 ⟨hF, Or.inl x⟩
    have hL : ¬ S L := fun x => h1 ⟨hF, Or.inr (Or.inl x)⟩
    have hV : ¬ S V := fun x => h1 ⟨hF, Or.inr (Or.inr (Or.inl x))⟩
    by_cases hIP : S IP
    · have hCM : ¬ S CM := fun x => h1 ⟨hF, Or.inr (Or.inr (Or.inr ⟨x, hIP⟩))⟩
      exact out_of closed_noHC_F2_L_V_CM (fun a ha hm => by
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hm
        rcases hm with rfl | rfl | rfl | rfl | rfl
        · exact hHC ha
        · exact hF2 ha
        · exact hL ha
        · exact hV ha
        · exact hCM ha) h (by simp)
    · exact out_of closed_noHC_F2_L_V_IP (fun a ha hm => by
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hm
        rcases hm with rfl | rfl | rfl | rfl | rfl
        · exact hHC ha
        · exact hF2 ha
        · exact hL ha
        · exact hV ha
        · exact hIP ha) h (by simp)
  · by_cases hL : S L
    · have hM : ¬ S M := fun x => h2 ⟨hL, x⟩
      exact out_of closed_noHC_M_F3P (fun a ha hm => by
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hm
        rcases hm with rfl | rfl | rfl
        · exact hHC ha
        · exact hM ha
        · exact hF ha) h (by simp)
    · exact out_of closed_noHC_L_F3P (fun a ha hm => by
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hm
        rcases hm with rfl | rfl | rfl
        · exact hHC ha
        · exact hL ha
        · exact hF ha) h (by simp)

/-- A route that avoids (F3') contains both L and M. -/
theorem bypass (S : St → Prop) (hHC : ¬ S HC) (hF3 : ¬ S F3P)
    (h : Derivable S HC) : S L ∧ S M := by
  rcases routes S hHC h with ⟨hF, _⟩ | hLM
  · exact absurd hF hF3
  · exact hLM

-- the five routes do give the conjecture

private theorem mem_rules {r : Rule} (h : r ∈ rules := by decide) : r ∈ rules := h

private theorem d {S : St → Prop} {a : St} (h : S a) : Derivable S a := .base h

private theorem one {S : St → Prop} {a b : St} (hr : (⟨[a], b⟩ : Rule) ∈ rules)
    (h : Derivable S a) : Derivable S b :=
  .rule (r := ⟨[a], b⟩) hr (by
    intro p hp
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
    subst hp; exact h)

private theorem two {S : St → Prop} {a b c : St} (hr : (⟨[a, b], c⟩ : Rule) ∈ rules)
    (ha : Derivable S a) (hb : Derivable S b) : Derivable S c :=
  .rule (r := ⟨[a, b], c⟩) hr (by
    intro p hp
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl
    · exact ha
    · exact hb)

theorem route_F2 : Derivable (fun a => a = F2 ∨ a = F3P) HC :=
  two (a := F2) (b := F3P) mem_rules (d (Or.inl rfl)) (d (Or.inr rfl))

theorem route_L : Derivable (fun a => a = L ∨ a = F3P) HC :=
  two (a := F2) (b := F3P) mem_rules
    (one (a := L) mem_rules (d (Or.inl rfl))) (d (Or.inr rfl))

theorem route_V : Derivable (fun a => a = V ∨ a = F3P) HC :=
  two (a := F2) (b := F3P) mem_rules
    (one (a := V) mem_rules (d (Or.inl rfl))) (d (Or.inr rfl))

theorem route_CM_IP : Derivable (fun a => a = CM ∨ a = IP ∨ a = F3P) HC :=
  two (a := F2) (b := F3P) mem_rules
    (two (a := CM) (b := IP) mem_rules (d (Or.inl rfl)) (d (Or.inr (Or.inl rfl))))
    (d (Or.inr (Or.inr rfl)))

theorem route_LM : Derivable (fun a => a = L ∨ a = M) HC :=
  two (a := L) (b := M) mem_rules (d (Or.inl rfl)) (d (Or.inr rfl))

/-! ## Part 2: the counting lemma of the switch lemma

For two columns `x`, `y` of signs (true = +1) of the same length, the number
of rows with `(+, -)` minus the number with `(-, +)` is the number of `+` in
`x` minus the number in `y`.  So when the column sums agree, the rows to be
switched come in pairs, which is what the column correction uses. -/

def mism : List Bool → List Bool → Int
  | a :: as, b :: bs =>
      (if a = true ∧ b = false then 1 else if a = false ∧ b = true then -1 else 0)
        + mism as bs
  | _, _ => 0

def plus : List Bool → Int
  | [] => 0
  | a :: as => (if a then 1 else 0) + plus as

theorem mism_eq : ∀ (x y : List Bool), x.length = y.length →
    mism x y = plus x - plus y
  | [], [], _ => by simp [mism, plus]
  | a :: as, b :: bs, h => by
      have ih := mism_eq as bs (by simpa using h)
      cases a <;> cases b <;> simp [mism, plus, ih] <;> omega
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

theorem switch_pairs (x y : List Bool) (hl : x.length = y.length)
    (hs : plus x = plus y) : mism x y = 0 := by
  rw [mism_eq x y hl, hs]; omega

/-! ## Part 3: dimension counts -/

/-- The Prym locus (dimension 3n) is a proper part of the Weil family
(dimension n^2) exactly when n >= 4. -/
theorem prym_proper (n : Nat) : 3 * n < n * n ↔ 4 ≤ n := by
  constructor
  · intro h
    apply Classical.byContradiction
    intro hn
    have : n ≤ 3 := by omega
    have : n * n ≤ 3 * n := Nat.mul_le_mul_right n this
    omega
  · intro h
    have : 4 * n ≤ n * n := Nat.mul_le_mul_right n h
    omega

/-- The count of Remark 5.13: for m >= 4 and every k,
3(m+k) + 3k < (m+k)^2. -/
theorem complement_count (m k : Nat) (hm : 4 ≤ m) :
    3 * (m + k) + 3 * k < (m + k) * (m + k) := by
  have h1 : 4 * m ≤ m * m := Nat.mul_le_mul_right m hm
  have h2 : 4 * k ≤ m * k := Nat.mul_le_mul_right k hm
  have h3 : (m + k) * (m + k) = m * m + m * k + (k * m + k * k) := by
    rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]
  have h4 : k * m = m * k := Nat.mul_comm k m
  omega

/-- Proposition 5.15: a cyclic triple cover of a curve of genus q, branched at
r points, whose Prym variety has dimension 2n satisfies 2q + r = 2n + 2; its
family has dimension q + 2n - 1, which is at most 3n, with equality exactly
for the etale covers (r = 0). -/
theorem branched_count (n q r : Nat) (h : 2 * q + r = 2 * n + 2) :
    q + 2 * n ≤ 3 * n + 1 ∧ (q + 2 * n = 3 * n + 1 ↔ r = 0) := by
  constructor
  · omega
  · constructor <;> intro _ <;> omega

/-- With Prym varieties of dimension 2n and n >= 4, the families of
Proposition 5.15 have dimension below n^2. -/
theorem branched_proper (n q r : Nat) (h : 2 * q + r = 2 * n + 2) (hn : 4 ≤ n) :
    q + 2 * n < n * n + 1 := by
  have h1 := (branched_count n q r h).1
  have h2 := (prym_proper n).2 hn
  omega

/-- Proposition 5.16: sigma acts on V_j = H^0(K_X + jL) by kappa^j, so the
invariant summands V_a (x) V_b of H^0(K_C) (x) (V_1 + V_2), those with
a + b = 0 mod 3, are V_1 (x) V_2 and V_2 (x) V_1. -/
theorem abelprym_pairs :
    ((List.range 3).flatMap fun a =>
      ([1, 2].filter fun b => (a + b) % 3 == 0).map fun b => (a, b)) =
      [(1, 2), (2, 1)] := by
  decide

/-- Proposition 5.16: for g = n + 1 the spaces H^0(K_X + jL) of dimensions g,
g - 1, g - 1 add up to the genus 3g - 2 of C, the invariant part E has
dimension 2n^2, and h^0(2K_X) = 3g - 3 = 3n. -/
theorem abelprym_dims (n : Nat) :
    (n + 1) + n + n = 3 * (n + 1) - 2 ∧ n * n + n * n = 2 * (n * n) ∧
      3 * (n + 1) - 3 = 3 * n :=
  ⟨by omega, (Nat.two_mul _).symm, by omega⟩

/-! ## Part 4: Picard numbers of Fermat surfaces

A character of the Fermat surface of degree m is a = (a0, a1, a2, a3) with
0 < ai < m and sum divisible by m; it is a Hodge class when the sum of the
residues of t*a is 2m for every unit t mod m.  The Picard number is one more
than the number of such characters. -/

def resid (m t a : Nat) : Nat := (t * a) % m

def isHodge (m : Nat) (a : List Nat) : Bool :=
  (List.range m).all fun t =>
    Nat.gcd t m != 1 || (a.map (resid m t)).foldl (· + ·) 0 == 2 * m

def fermatChars (m : Nat) : List (List Nat) :=
  (List.range (m - 1)).flatMap fun i => (List.range (m - 1)).flatMap fun j =>
    (List.range (m - 1)).filterMap fun k =>
      let s := (i + 1) + (j + 1) + (k + 1)
      if s % m == 0 then none else some [i + 1, j + 1, k + 1, m - s % m]

def picard (m : Nat) : Nat := ((fermatChars m).filter (isHodge m)).length + 1

theorem picard_quartic : picard 4 = 20 := by decide
theorem picard_quintic : picard 5 = 37 := by decide
theorem picard_sextic : picard 6 = 86 := by decide

/-! ## Part 5: the exceptional orbits for odd degrees divisible by 3

A multiset of residues mod m is a list of numbers in [0, m).  It is balanced
when its sum is divisible by m and the residues of t*a add up to (length)*m/2
for every unit t.  A move (l, x) for a sextuple a, with l an odd prime
dividing m and l*x nonzero, replaces the elements of the fiber
{x + j m/l} that lie in a by the negatives of the other elements of the
fiber, together with l*x; it is direct if at most four elements remain, and
lowering if six remain and the orders, sorted downwards, decrease
lexicographically. -/

def sumL (a : List Nat) : Nat := a.foldl (· + ·) 0

def balancedB (m : Nat) (a : List Nat) : Bool :=
  sumL a % m == 0 &&
  (List.range m).all fun t =>
    Nat.gcd t m != 1 || 2 * sumL (a.map (resid m t)) == a.length * m

def hasPairB (m : Nat) : List Nat → Bool
  | [] => false
  | x :: xs => xs.any (fun y => (x + y) % m == 0) || hasPairB m xs

def generatesB (m : Nat) (a : List Nat) : Bool := a.foldl Nat.gcd m == 1

def insertDesc (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: ys => if y ≤ x then x :: y :: ys else y :: insertDesc x ys

def sortDesc : List Nat → List Nat
  | [] => []
  | x :: xs => insertDesc x (sortDesc xs)

def lexLt : List Nat → List Nat → Bool
  | x :: xs, y :: ys => x < y || (x == y && lexLt xs ys)
  | _, _ => false

def profileL (m : Nat) (a : List Nat) : List Nat := sortDesc (a.map fun x => m / Nat.gcd x m)

def isPrimeB (p : Nat) : Bool := 2 ≤ p && (List.range p).all fun q => q < 2 || p % q != 0

/-- Does the sextuple `a` have a lowering move (`low = true`) or a direct move? -/
def moveB (m : Nat) (a : List Nat) (low : Bool) : Bool :=
  (List.range (m + 1)).any fun l =>
    l % 2 == 1 && 3 ≤ l && m % l == 0 && isPrimeB l &&
    (List.range (m / l)).any fun x =>
      let fib := (List.range l).map fun j => (x + j * (m / l)) % m
      let s := fib.filter fun y => a.contains y
      let rest := fib.filter fun y => !a.contains y
      let b := s.foldl (fun b y => b.erase y) a ++ rest.map (fun y => (m - y) % m) ++ [l * x % m]
      l * x % m != 0 &&
      (if low then 7 + l - 2 * s.length == 6 && lexLt (profileL m b) (profileL m a)
       else 7 + l - 2 * s.length ≤ 4)

def O21 : List Nat := [1, 4, 9, 15, 16, 18]
def O33 : List Nat := [1, 4, 16, 22, 25, 31]
def O39 : List Nat := [1, 7, 16, 22, 34, 37]

def exceptionalOK (m : Nat) (o : List Nat) : Bool :=
  balancedB m o && !hasPairB m o && generatesB m o && !moveB m o false && !moveB m o true

theorem o21_exceptional : exceptionalOK 21 O21 = true := by decide
theorem o33_exceptional : exceptionalOK 33 O33 = true := by decide
theorem o39_exceptional : exceptionalOK 39 O39 = true := by decide

/-- Aoki's 2-standard quadruple at the even level M = 2m'. -/
def T2 (M x : Nat) : List Nat := [x, (x + M / 2) % M, (M - 2 * x % M) % M, M / 2]

def sameMultiset (a b : List Nat) : Bool := sortDesc a == sortDesc b

/-- O21 + {2, 19} = sigma(3,2) + Q at level 21, with sigma(3,2) and Q balanced. -/
theorem o21_identity :
    (sameMultiset (O21 ++ [2, 19]) ([2, 9, 16, 15] ++ [1, 4, 18, 19]) &&
      balancedB 21 [2, 9, 16, 15] && balancedB 21 [1, 4, 18, 19]) = true := by decide

/-- 2 O33 + {1,65} + {25,41} + {33,33} = Q + T(32) + T(8) at level 66, all parts balanced. -/
theorem o33_identity :
    (sameMultiset (O33.map (2 * ·) ++ [1, 65, 25, 41, 33, 33])
        ([1, 25, 44, 62] ++ T2 66 32 ++ T2 66 8) &&
      balancedB 66 (O33.map (2 * ·)) && balancedB 66 [1, 25, 44, 62] &&
      balancedB 66 (T2 66 32) && balancedB 66 (T2 66 8)) = true := by decide

/-- 2 O39 + {5,73} + {7,71} + {39,39} = Q + T(32) + T(5) at level 78, all parts balanced. -/
theorem o39_identity :
    (sameMultiset (O39.map (2 * ·) ++ [5, 73, 7, 71, 39, 39])
        ([2, 7, 73, 74] ++ T2 78 32 ++ T2 78 5) &&
      balancedB 78 (O39.map (2 * ·)) && balancedB 78 [2, 7, 73, 74] &&
      balancedB 78 (T2 78 32) && balancedB 78 (T2 78 5)) = true := by decide

#print axioms routes
#print axioms bypass
#print axioms countermodel
#print axioms schoen_alone
#print axioms route_LM
#print axioms route_L
#print axioms route_CM_IP
#print axioms switch_pairs
#print axioms complement_count
#print axioms branched_count
#print axioms branched_proper
#print axioms abelprym_pairs
#print axioms abelprym_dims
#print axioms picard_sextic
#print axioms o21_exceptional
#print axioms o33_exceptional
#print axioms o39_exceptional
#print axioms o21_identity
#print axioms o33_identity
#print axioms o39_identity

end Closure
