import FermatHodge.Sextuple

/-!
# The Hodge conjecture for Fermat fourfolds of degree prime to `6`

Let `X_m ⊂ ℙ⁵` be the Fermat fourfold of degree `m`.  By Shioda, the primitive rational Hodge
classes in `H⁴(X_m)` are spanned by the eigenclasses of the characters `α ∈ (ZMod m)⁶` with
nonzero entries, sum zero, and `∑ ⟨t αᵢ⟩ = 3m` for every unit `t` (here `⟨·⟩` is the
representative in `[0, m)`).  The eigenclass of a decomposable character (`αᵢ + αⱼ = 0` for some
`i ≠ j`) is algebraic by the inductive structure of Fermat varieties (Shioda, Ran), and the
eigenclass of a `5`-standard character is algebraic by Aoki (1987, Theorem 2-1).

This file proves the combinatorial step: for `m` prime to `6`, every Hodge character is
decomposable or `5`-standard.  The geometric facts above are not formalized (Mathlib has no
Hodge theory); they enter `hodge_fermat_fourfold` as hypotheses about an abstract predicate
`Alg` ("the eigenclass of `α` is algebraic").  The analytic input `BernoulliNV`
(`B_{1,χ} ≠ 0` for odd primitive `χ`) is also a hypothesis.
-/

open Finset

noncomputable section

namespace FermatHodge

open Classical

set_option linter.unusedSectionVars false

variable {m : ℕ} [NeZero m]

/-- Hodge characters of the Fermat variety of dimension `n - 2` and degree `m`, as `n`-tuples. -/
def IsHodge {n : ℕ} (α : Fin n → ZMod m) : Prop :=
  (∀ i, α i ≠ 0) ∧ ∑ i, α i = 0 ∧
    ∀ t : (ZMod m)ˣ, ∑ i, ((t : ZMod m) * α i).val = (n / 2) * m

/-- Decomposable characters: two entries add up to zero. -/
def Decomposable {n : ℕ} (α : Fin n → ZMod m) : Prop := ∃ i j, i ≠ j ∧ α i + α j = 0

/-- `5`-standard characters: up to order, `(x, x + m/5, x + 2m/5, x + 3m/5, x + 4m/5, -5x)`. -/
def Standard5 (α : Fin 6 → ZMod m) : Prop := Std5 ((univ : Finset (Fin 6)).val.map α)

lemma decomposable_of_pair (hm2 : ¬2 ∣ m) {n : ℕ} {α : Fin n → ZMod m} (h0 : ∀ i, α i ≠ 0)
    (h : ∃ a ∈ (univ : Finset (Fin n)).val.map α, -a ∈ (univ : Finset (Fin n)).val.map α) :
    Decomposable α := by
  obtain ⟨a, ha, hna⟩ := h
  simp only [Multiset.mem_map, Finset.mem_val, mem_univ, true_and] at ha hna
  obtain ⟨i, rfl⟩ := ha
  obtain ⟨j, hj⟩ := hna
  refine ⟨i, j, fun hij => ?_, by rw [hj, add_neg_cancel]⟩
  subst hij
  have hcop2 : Nat.Coprime 2 m := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hm2
  apply h0 i
  apply eq_zero_of_coprime_mul hcop2
  push_cast
  linear_combination hj

lemma tuple_facts {n : ℕ} (α : Fin n → ZMod m) :
    Multiset.card ((univ : Finset (Fin n)).val.map α) = n ∧
    ((univ : Finset (Fin n)).val.map α).sum = ∑ i, α i ∧
    ∀ t : (ZMod m)ˣ, (((univ : Finset (Fin n)).val.map α).map
      fun a => ((t : ZMod m) * a).val).sum = ∑ i, ((t : ZMod m) * α i).val := by
  refine ⟨by simp, (Finset.sum_eq_multiset_sum _ _).symm, fun t => ?_⟩
  rw [Multiset.map_map, Finset.sum_eq_multiset_sum]
  rfl

/-- **Classification of Hodge characters of Fermat fourfolds of degree prime to `6`.** -/
theorem hodge_sextuple (hm2 : ¬2 ∣ m) (hm3 : ¬3 ∣ m) (hB : BernoulliNV) (α : Fin 6 → ZMod m)
    (hα : IsHodge α) : Decomposable α ∨ Standard5 α := by
  obtain ⟨h0, hs, hH⟩ := hα
  obtain ⟨hc, hsum, hmap⟩ := tuple_facts α
  rcases sextuple hm2 hm3 hB _ hc (hsum.trans hs) (6 / 2 * m) (fun t => (hmap t).trans (hH t))
    with h | h
  · exact Or.inl (decomposable_of_pair hm2 h0 h)
  · exact Or.inr h

/-- **Hodge characters of Fermat surfaces of degree prime to `6` are decomposable.** -/
theorem hodge_quadruple (hm2 : ¬2 ∣ m) (hm3 : ¬3 ∣ m) (hB : BernoulliNV) (α : Fin 4 → ZMod m)
    (hα : IsHodge α) : Decomposable α := by
  obtain ⟨h0, hs, hH⟩ := hα
  obtain ⟨hc, hsum, hmap⟩ := tuple_facts α
  exact decomposable_of_pair hm2 h0
    (quadruple hm2 hm3 hB _ hc (hsum.trans hs) (4 / 2 * m) (fun t => (hmap t).trans (hH t)))

/-- **The Hodge conjecture for the Fermat fourfold of degree `m` prime to `6`**, relative to the
geometric inputs: if decomposable and `5`-standard characters have algebraic eigenclasses, then
every Hodge character does. -/
theorem hodge_fermat_fourfold (hm2 : ¬2 ∣ m) (hm3 : ¬3 ∣ m) (hB : BernoulliNV)
    (Alg : (Fin 6 → ZMod m) → Prop)
    (hdec : ∀ α, IsHodge α → Decomposable α → Alg α)
    (hstd : ∀ α, IsHodge α → Standard5 α → Alg α) :
    ∀ α, IsHodge α → Alg α := by
  intro α hα
  rcases hodge_sextuple hm2 hm3 hB α hα with h | h
  · exact hdec α hα h
  · exact hstd α hα h

end FermatHodge
