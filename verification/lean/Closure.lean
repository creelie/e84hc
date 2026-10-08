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
#print axioms picard_sextic

end Closure
