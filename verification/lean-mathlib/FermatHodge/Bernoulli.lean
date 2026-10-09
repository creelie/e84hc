import FermatHodge.Fermat

/-!
# The nonvanishing of `B_{1,χ}`

For an odd primitive Dirichlet character `χ` modulo `N`, the sum `∑ χ(s) s` over the units does
not vanish.  This is the hypothesis `BernoulliNV` of the classification.  The proof follows the
classical route from `L(1, χ̄) ≠ 0`, which Mathlib provides
(`DirichletCharacter.LFunction_apply_one_ne_zero`):

* `tendsto_log_series`: `∑ wⁿ / n = -log (1 - w)` for `‖w‖ = 1`, `w ≠ 1` (Dirichlet's test and
  Abel's limit theorem);
* `tendsto_LFunction_one`: Mathlib's `L(1, χ)` is the sum of the conditionally convergent series
  `∑ χ(n) / n` for `χ ≠ 1` (summation by parts, uniformly for `σ ∈ [1, 2]`);
* `arg_one_sub_exp`: `arg (1 - e^{iθ}) = θ/2 - π/2` for `0 < θ < 2π`;
* `Bsum_ne_zero`: expanding `χ̄(n)` by the Gauss sum gives
  `τ(χ) L(1, χ̄) = -i (π / N) ∑ χ(s) s`, so the sum vanishes only if `L(1, χ̄)` does.

The last section restates the main theorems without the hypothesis.
-/

open Complex Filter Topology Finset

noncomputable section

namespace FermatHodge




/-- Partial sums of a geometric series on the unit circle are bounded. -/
lemma norm_geom_partial_le {w : ℂ} (hw1 : ‖w‖ = 1) (hw : w ≠ 1) (n : ℕ) :
    ‖∑ i ∈ range n, w ^ (i + 1)‖ ≤ 2 / ‖w - 1‖ := by
  have hne : w - 1 ≠ 0 := sub_ne_zero.mpr hw
  have hpos : 0 < ‖w - 1‖ := norm_pos_iff.mpr hne
  have h : ∑ i ∈ range n, w ^ (i + 1) = w * ((w ^ n - 1) / (w - 1)) := by
    rw [← geom_sum_eq hw, mul_sum]
    exact sum_congr rfl (fun i _ => by ring)
  rw [h, norm_mul, hw1, one_mul, norm_div, div_le_div_iff_of_pos_right hpos]
  calc ‖w ^ n - 1‖ ≤ ‖w ^ n‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by rw [norm_pow, hw1, one_pow, norm_one]; norm_num

/-- The logarithmic series converges at every point of the unit circle other than `1`. -/
theorem tendsto_log_series {w : ℂ} (hw1 : ‖w‖ = 1) (hw : w ≠ 1) :
    Tendsto (fun M => ∑ n ∈ range M, w ^ (n + 1) / (n + 1)) atTop (𝓝 (-log (1 - w))) := by
  -- Dirichlet's test gives a limit `l`
  have hcs : CauchySeq fun M => ∑ n ∈ range M, (1 / ((n : ℝ) + 1)) • w ^ (n + 1) := by
    refine Antitone.cauchySeq_series_mul_of_tendsto_zero_of_bounded (b := 2 / ‖w - 1‖) ?_ ?_
      (norm_geom_partial_le hw1 hw)
    · intro a b hab
      apply one_div_le_one_div_of_le (by positivity)
      exact_mod_cast Nat.add_le_add_right hab 1
    · exact tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨l, hl⟩ := cauchySeq_tendsto_of_complete hcs
  have hsame : ∀ M, ∑ n ∈ range M, (1 / ((n : ℝ) + 1)) • w ^ (n + 1) =
      ∑ n ∈ range M, w ^ (n + 1) / (n + 1) := fun M => by
    refine sum_congr rfl (fun n _ => ?_)
    rw [Complex.real_smul]; push_cast; ring
  simp_rw [hsame] at hl
  -- Abel's theorem identifies `l`
  set f : ℕ → ℂ := fun n => w ^ n / n with hf
  have hfl : Tendsto (fun M => ∑ i ∈ range M, f i) atTop (𝓝 l) := by
    have : Tendsto (fun M => ∑ i ∈ range (M + 1), f i) atTop (𝓝 l) := by
      refine hl.congr (fun M => ?_)
      rw [sum_range_succ']
      simp [hf]
    exact (tendsto_add_atTop_iff_nat 1).mp this
  have habel := Complex.tendsto_tsum_powerSeries_nhdsWithin_lt hfl
  have hval : ∀ᶠ z in (𝓝[<] (1 : ℝ)).map ofReal, ∑' n, f n * z ^ n = -log (1 - w * z) := by
    rw [eventually_map]
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with r hr
    have hz : ‖w * (r : ℂ)‖ < 1 := by
      rw [norm_mul, hw1, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr.1]
      exact hr.2
    rw [← (hasSum_taylorSeries_neg_log hz).tsum_eq]
    exact tsum_congr (fun n => by simp only [hf]; rw [mul_pow]; ring)
  have hcont : Tendsto (fun z : ℂ => -log (1 - w * z)) ((𝓝[<] (1 : ℝ)).map ofReal)
      (𝓝 (-log (1 - w))) := by
    have hslit : 1 - w ∈ slitPlane := by
      left
      have hre : w.re < 1 := by
        by_contra hc
        push Not at hc
        have h1 : w.re ≤ ‖w‖ := Complex.re_le_norm w
        have hre1 : w.re = 1 := by linarith
        have him : w.im = 0 := by
          have := Complex.sq_norm w
          rw [hw1, Complex.normSq_apply] at this
          nlinarith [sq_nonneg w.im]
        exact hw (Complex.ext (by simp [hre1]) (by simp [him]))
      simp; linarith
    have hc : ContinuousAt (fun z : ℂ => -log (1 - w * z)) 1 := by
      have : ContinuousAt (fun z : ℂ => 1 - w * z) 1 := by fun_prop
      have hlog := (continuousAt_clog (by simpa using hslit)).comp (f := fun z : ℂ => 1 - w * z)
        (x := 1) this
      exact hlog.neg
    have hmap : (𝓝[<] (1 : ℝ)).map ofReal ≤ 𝓝 (1 : ℂ) := by
      have : Tendsto ofReal (𝓝[<] (1 : ℝ)) (𝓝 ((1 : ℝ) : ℂ)) :=
        (Complex.continuous_ofReal.tendsto 1).mono_left nhdsWithin_le_nhds
      rw [ofReal_one] at this
      exact this
    simpa using hc.tendsto.mono_left hmap
  have hne : ((𝓝[<] (1 : ℝ)).map ofReal).NeBot := by
    exact Filter.NeBot.map inferInstance _
  have := tendsto_nhds_unique (habel.congr' hval) hcont
  rw [this] at hl
  exact hl





/-- Partial sums of a function on `ZMod N` with total sum zero, along `1, 2, 3, ...`, are
bounded. -/
lemma sum_range_shift_eq {N : ℕ} [NeZero N] (f : ZMod N → ℂ) (c : ℕ) :
    ∑ i ∈ range N, f ((c + i : ℕ) : ZMod N) = ∑ x, f x := by
  rw [Finset.sum_range (fun i => f ((c + i : ℕ) : ZMod N))]
  refine Fintype.sum_bijective (fun i : Fin N => ((c + i : ℕ) : ZMod N)) ?_ _ _ (fun _ => rfl)
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨fun i j hij => ?_, by simp [ZMod.card]⟩
  simp only [Nat.cast_add] at hij
  have h := add_left_cancel hij
  have := congrArg ZMod.val h
  rw [ZMod.val_cast_of_lt i.2, ZMod.val_cast_of_lt j.2] at this
  exact Fin.ext this

lemma bounded_partial_sums {N : ℕ} [NeZero N] (f : ZMod N → ℂ) (hf : ∑ x, f x = 0) :
    ∃ B, ∀ n, ‖∑ i ∈ range n, f ((i + 1 : ℕ) : ZMod N)‖ ≤ B := by
  set P : ℕ → ℂ := fun n => ∑ i ∈ range n, f ((i + 1 : ℕ) : ZMod N) with hP
  have hper : ∀ n, P (n + N) = P n := by
    intro n
    simp only [hP]
    rw [sum_range_add]
    have := sum_range_shift_eq f (n + 1)
    rw [hf] at this
    rw [show (∑ x ∈ range N, f ((n + x + 1 : ℕ) : ZMod N)) = 0 by
      rw [← this]; exact sum_congr rfl (fun i _ => by congr 2; ring), add_zero]
  have hmod : ∀ q r, P (r + N * q) = P r := by
    intro q r
    induction q with
    | zero => simp
    | succ q ih => rw [mul_add, mul_one, ← add_assoc, hper, ih]
  refine ⟨∑ r ∈ range N, ‖P r‖, fun n => ?_⟩
  have hn : P n = P (n % N) := by
    conv_lhs => rw [← Nat.mod_add_div n N]
    exact hmod _ _
  rw [show ∑ i ∈ range n, f ((i + 1 : ℕ) : ZMod N) = P n from rfl, hn]
  exact Finset.single_le_sum (f := fun r => ‖P r‖) (fun _ _ => norm_nonneg _)
    (mem_range.mpr (Nat.mod_lt n (Nat.pos_of_ne_zero (NeZero.ne N))))

/-- The weights `(n + 1) ^ (-σ)`. -/
def wt (σ : ℝ) (n : ℕ) : ℝ := ((n : ℝ) + 1) ^ (-σ)

lemma wt_nonneg (σ : ℝ) (n : ℕ) : 0 ≤ wt σ n := by
  unfold wt; positivity

lemma wt_succ_le (σ : ℝ) (hσ : 0 ≤ σ) (n : ℕ) : wt σ (n + 1) ≤ wt σ n := by
  unfold wt
  push_cast
  apply Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)

lemma tendsto_wt {σ : ℝ} (hσ : 0 < σ) : Tendsto (wt σ) atTop (𝓝 0) := by
  have h1 := tendsto_rpow_neg_atTop hσ
  have h2 : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  exact h1.comp h2

/-- The differences of the weights, uniformly for `σ ∈ [1, 2]`. -/
lemma wt_sub_le {σ : ℝ} (h1 : 1 ≤ σ) (h2 : σ ≤ 2) (n : ℕ) :
    wt σ n - wt σ (n + 1) ≤ 2 / ((n : ℝ) + 1) ^ 2 := by
  unfold wt
  set x : ℝ := (n : ℝ) + 1 with hx
  have hx1 : 1 ≤ x := by simp [hx]
  have hx0 : 0 < x := by linarith
  have hy : ((n + 1 : ℕ) : ℝ) + 1 = x + 1 := by push_cast; ring
  rw [hy]
  have hy0 : 0 < x + 1 := by linarith
  -- Bernoulli: (x/(x+1))^σ ≥ 1 - σ/(x+1)
  have hb := one_add_mul_self_le_rpow_one_add (s := -1 / (x + 1)) (p := σ)
    (by rw [neg_div, neg_le_neg_iff, div_le_one hy0]; linarith) h1
  have hq : 1 + -1 / (x + 1) = x / (x + 1) := by field_simp; ring
  rw [hq, Real.div_rpow hx0.le hy0.le] at hb
  have hxs : 0 < x ^ σ := Real.rpow_pos_of_pos hx0 σ
  have hys : 0 < (x + 1) ^ σ := Real.rpow_pos_of_pos hy0 σ
  rw [Real.rpow_neg hx0.le, Real.rpow_neg hy0.le]
  -- (x+1)^{-σ} ≥ x^{-σ} (1 - σ/(x+1))
  have key : (x ^ σ)⁻¹ - ((x + 1) ^ σ)⁻¹ ≤ (x ^ σ)⁻¹ * (σ / (x + 1)) := by
    have : ((x + 1) ^ σ)⁻¹ = (x ^ σ)⁻¹ * (x ^ σ / (x + 1) ^ σ) := by field_simp
    rw [this]
    have hxi : 0 < (x ^ σ)⁻¹ := inv_pos.mpr hxs
    have hb' : 1 - σ / (x + 1) ≤ x ^ σ / (x + 1) ^ σ := by
      have : σ * (-1 / (x + 1)) = -(σ / (x + 1)) := by ring
      linarith
    have := mul_le_mul_of_nonneg_left hb' hxi.le
    rw [mul_sub, mul_one] at this
    linarith
  have hxσ : (x ^ σ)⁻¹ ≤ x⁻¹ := by
    rw [← Real.rpow_neg hx0.le, ← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  calc (x ^ σ)⁻¹ - ((x + 1) ^ σ)⁻¹ ≤ (x ^ σ)⁻¹ * (σ / (x + 1)) := key
    _ ≤ x⁻¹ * (2 / x) := by
        apply mul_le_mul hxσ _ (by positivity) (by positivity)
        rw [div_le_div_iff₀ hy0 hx0]; nlinarith
    _ = 2 / x ^ 2 := by field_simp


section abel

variable {a : ℕ → ℂ} {B : ℝ}

/-- The Abel-summed form of the Dirichlet series `∑ a n (n + 1) ^ (-σ)`. -/
def Gs (a : ℕ → ℂ) (σ : ℝ) : ℂ :=
  -∑' i, (∑ j ∈ range (i + 1), a j) * ((wt σ (i + 1) - wt σ i : ℝ) : ℂ)

lemma summable_two_div_sq : Summable (fun i : ℕ => 2 / ((i : ℝ) + 1) ^ 2) := by
  have h : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) := Real.summable_one_div_nat_pow.mpr one_lt_two
  have h1 := (summable_nat_add_iff 1).mpr h
  refine (h1.mul_left 2).congr (fun i => ?_)
  push_cast; ring

lemma norm_term_le (hB : ∀ n, ‖∑ i ∈ range n, a i‖ ≤ B) {σ : ℝ} (h1 : 1 ≤ σ) (h2 : σ ≤ 2)
    (i : ℕ) :
    ‖(∑ j ∈ range (i + 1), a j) * ((wt σ (i + 1) - wt σ i : ℝ) : ℂ)‖ ≤
      B * (2 / ((i : ℝ) + 1) ^ 2) := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonpos (sub_nonpos.mpr (wt_succ_le σ (by linarith) i)), neg_sub]
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0)
  exact mul_le_mul (hB _) (wt_sub_le h1 h2 i)
    (sub_nonneg.mpr (wt_succ_le σ (by linarith) i)) hB0

/-- Summation by parts: the partial sums of the Dirichlet series converge to `Gs a σ`. -/
lemma tendsto_partial_Gs (hB : ∀ n, ‖∑ i ∈ range n, a i‖ ≤ B) {σ : ℝ} (h1 : 1 ≤ σ)
    (h2 : σ ≤ 2) :
    Tendsto (fun M => ∑ n ∈ range M, a n * (wt σ n : ℂ)) atTop (𝓝 (Gs a σ)) := by
  have hparts : ∀ M, ∑ n ∈ range M, a n * (wt σ n : ℂ) =
      (∑ i ∈ range M, a i) * (wt σ (M - 1) : ℂ) -
        ∑ i ∈ range (M - 1), (∑ j ∈ range (i + 1), a j) * ((wt σ (i + 1) - wt σ i : ℝ) : ℂ) := by
    intro M
    have := Finset.sum_range_by_parts' (f := a) (g := fun n => (wt σ n : ℂ)) M
    simp only [smul_eq_mul] at this
    rw [this]
    congr 1
    exact sum_congr rfl (fun i _ => by push_cast; ring)
  simp_rw [hparts]
  have hsum : Summable (fun i => (∑ j ∈ range (i + 1), a j) * ((wt σ (i + 1) - wt σ i : ℝ) : ℂ)) :=
    Summable.of_norm_bounded (summable_two_div_sq.mul_left B) (norm_term_le hB h1 h2)
  have hM1 : Tendsto (fun M : ℕ => M - 1) atTop atTop := tendsto_sub_atTop_nat 1
  have hA : Tendsto (fun M => (∑ i ∈ range M, a i) * (wt σ (M - 1) : ℂ)) atTop (𝓝 0) := by
    have hw : Tendsto (fun M => wt σ (M - 1)) atTop (𝓝 0) :=
      (tendsto_wt (by linarith)).comp hM1
    refine squeeze_zero_norm (fun M => ?_) (by simpa using hw.const_mul B)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (wt_nonneg _ _)]
    exact mul_le_mul_of_nonneg_right (hB M) (wt_nonneg _ _)
  have hT := (hsum.hasSum.tendsto_sum_nat).comp hM1
  have := hA.sub hT
  rw [zero_sub] at this
  exact this

lemma continuousOn_Gs (hB : ∀ n, ‖∑ i ∈ range n, a i‖ ≤ B) :
    ContinuousOn (Gs a) (Set.Icc 1 2) := by
  have hc : ∀ n : ℕ, Continuous (fun σ : ℝ => wt σ n) := fun n => by
    unfold wt
    exact continuous_const.rpow continuous_neg (fun _ => Or.inl (by positivity))
  refine (continuousOn_tsum (fun i => ?_) (summable_two_div_sq.mul_left B)
    (fun i σ hσ => norm_term_le hB hσ.1 hσ.2 i)).neg
  exact (continuous_const.mul (Complex.continuous_ofReal.comp
    ((hc (i + 1)).sub (hc i)))).continuousOn

end abel

/-- The value at `1` of the `L`-function of a nontrivial Dirichlet character is the sum of the
conditionally convergent series `∑ χ(n) / n`. -/
theorem tendsto_LFunction_one {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) :
    Tendsto (fun M => ∑ n ∈ range M, χ ((n + 1 : ℕ) : ZMod N) / ((n : ℂ) + 1)) atTop
      (𝓝 (χ.LFunction 1)) := by
  obtain ⟨B, hB⟩ := bounded_partial_sums (fun x => χ x) (MulChar.sum_eq_zero_of_ne_one hχ)
  set a : ℕ → ℂ := fun n => χ ((n + 1 : ℕ) : ZMod N) with ha
  have hB' : ∀ n, ‖∑ i ∈ range n, a i‖ ≤ B := hB
  -- for `σ ∈ (1, 2]` the L-function is `Gs a σ`
  have heq : ∀ σ : ℝ, 1 < σ → σ ≤ 2 → χ.LFunction σ = Gs a σ := by
    intro σ h1 h2
    have hs : 1 < ((σ : ℂ)).re := by simpa using h1
    rw [DirichletCharacter.LFunction_eq_LSeries χ hs]
    have hsum := (DirichletCharacter.LSeriesSummable_of_one_lt_re χ hs).hasSum
    have ht := (tendsto_add_atTop_iff_nat 1).mpr hsum.tendsto_sum_nat
    refine tendsto_nhds_unique (ht.congr (fun M => ?_)) (tendsto_partial_Gs hB' h1.le h2)
    rw [sum_range_succ']
    simp only [LSeries.term_def, Nat.add_eq_zero_iff, one_ne_zero, and_false,
      ite_false, ite_true, add_zero]
    refine sum_congr rfl (fun n _ => ?_)
    simp only [ha, wt]
    have hx : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
    rw [Real.rpow_neg hx, Complex.ofReal_inv, Complex.ofReal_cpow hx]
    push_cast
    rw [div_eq_mul_inv]
  have hG := (continuousOn_Gs hB' 1 ⟨le_refl _, one_le_two⟩).mono_of_mem_nhdsWithin
    (s := Set.Ioi 1) (mem_of_superset (Ioc_mem_nhdsGT one_lt_two) Set.Ioc_subset_Icc_self)
  have hL : Tendsto (fun σ : ℝ => χ.LFunction σ) (𝓝[>] 1) (𝓝 (χ.LFunction 1)) := by
    have hc := ((DirichletCharacter.differentiable_LFunction hχ).continuous.comp
      Complex.continuous_ofReal).tendsto 1
    have := hc.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 1))
    simp only [Function.comp_def, Complex.ofReal_one] at this
    exact this
  have hev : (fun σ : ℝ => χ.LFunction σ) =ᶠ[𝓝[>] 1] Gs a := by
    filter_upwards [Ioc_mem_nhdsGT one_lt_two] with σ hσ
    exact heq σ hσ.1 hσ.2
  have h1 : χ.LFunction 1 = Gs a 1 := tendsto_nhds_unique (hL.congr' hev) hG
  rw [h1]
  refine (tendsto_partial_Gs hB' le_rfl one_le_two).congr (fun M => sum_congr rfl (fun n _ => ?_))
  simp only [ha, wt, Real.rpow_neg_one]
  push_cast
  rw [div_eq_mul_inv]





/-- `1 - e^{iθ} = 2 sin(θ/2) e^{i(θ/2 - Real.pi/2)}`. -/
lemma one_sub_exp_eq (θ : ℝ) :
    1 - exp (θ * I) = ((2 * Real.sin (θ / 2) : ℝ) : ℂ) * exp (((θ / 2 - Real.pi / 2 : ℝ) : ℂ) * I) := by
  set E := exp ((θ : ℂ) / 2 * I) with hE
  have hE0 : E ≠ 0 := exp_ne_zero _
  have h1 : exp (θ * I) = E ^ 2 := by
    rw [hE, ← exp_nat_mul]; congr 1; push_cast; ring
  have h2 : exp (((θ / 2 - Real.pi / 2 : ℝ) : ℂ) * I) = E * (-I) := by
    have : (((θ / 2 - Real.pi / 2 : ℝ) : ℂ) * I) = (θ : ℂ) / 2 * I + (-(Real.pi / 2 * I)) := by
      push_cast; ring
    rw [this, exp_add, exp_neg, exp_pi_div_two_mul_I, inv_I]
  have h3 : ((2 * Real.sin (θ / 2) : ℝ) : ℂ) = (E⁻¹ - E) * I := by
    push_cast
    rw [Complex.sin, hE, ← exp_neg]
    have : -((θ : ℂ) / 2 * I) = -((θ : ℂ) / 2) * I := by ring
    rw [this]; ring
  rw [h1, h2, h3]
  field_simp
  ring_nf
  rw [I_sq]
  ring

/-- For `0 < θ < 2Real.pi`, `arg (1 - e^{iθ}) = θ / 2 - Real.pi / 2`. -/
lemma arg_one_sub_exp {θ : ℝ} (h0 : 0 < θ) (h1 : θ < 2 * Real.pi) :
    arg (1 - exp (θ * I)) = θ / 2 - Real.pi / 2 := by
  rw [one_sub_exp_eq, arg_real_mul _ (by
    have : 0 < Real.sin (θ / 2) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
    linarith), exp_mul_I]
  apply arg_cos_add_sin_mul_I
  constructor <;> linarith [Real.pi_pos]


section gauss

variable {N : ℕ} [NeZero N]

lemma norm_stdAddChar (x : ZMod N) : ‖(ZMod.stdAddChar x : ℂ)‖ = 1 := by
  rw [ZMod.stdAddChar_apply]; exact Circle.norm_coe _

lemma stdAddChar_ne_one {x : ZMod N} (hx : x ≠ 0) : (ZMod.stdAddChar x : ℂ) ≠ 1 := by
  intro h
  apply hx
  apply ZMod.injective_stdAddChar
  rw [h, AddChar.map_zero_eq_one]

lemma gaussSum_ne_zero_of_isPrimitive {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) :
    gaussSum χ ZMod.stdAddChar ≠ 0 := by
  intro h0
  have hF : ZMod.dft (⇑χ) = 0 := by
    funext k
    rw [hχ.fourierTransform_eq_inv_mul_gaussSum k, h0, mul_zero]
    rfl
  have h := congr_fun (ZMod.dft_dft (⇑χ)) (-1)
  rw [hF, map_zero, neg_neg, map_one] at h
  simp only [Pi.zero_apply, smul_eq_mul, mul_one] at h
  exact NeZero.ne (N : ℂ) h.symm

lemma inv_mul_gaussSum {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (n : ℕ) :
    χ⁻¹ (n : ZMod N) * gaussSum χ ZMod.stdAddChar =
      ∑ x, χ x * (ZMod.stdAddChar x : ℂ) ^ n := by
  rw [← gaussSum_mulShift_of_isPrimitive _ hχ, gaussSum]
  refine sum_congr rfl (fun x _ => ?_)
  rw [AddChar.mulShift_apply, ← AddChar.map_nsmul_eq_pow, nsmul_eq_mul]

lemma sum_eq_Bsum (χ : DirichletCharacter ℂ N) [Nontrivial (ZMod N)] :
    ∑ x : ZMod N, χ x * (x.val : ℂ) = Bsum χ := by
  unfold Bsum
  have hemb : ∑ s : (ZMod N)ˣ, χ s * ((s : ZMod N).val : ℂ) =
      ∑ x ∈ univ.map ⟨Units.val, Units.val_injective⟩, χ x * (x.val : ℂ) := by
    rw [sum_map]; rfl
  rw [hemb]
  refine (sum_subset (subset_univ _) (fun x _ hx => ?_)).symm
  have hnu : ¬IsUnit x := by
    rintro ⟨u, rfl⟩
    exact hx (mem_map.mpr ⟨u, mem_univ _, rfl⟩)
  rw [MulChar.map_nonunit χ hnu, zero_mul]

lemma arg_one_sub_stdAddChar {x : ZMod N} (hx : x ≠ 0) :
    arg (1 - ZMod.stdAddChar x) = Real.pi * x.val / N - Real.pi / 2 := by
  have hv : 0 < x.val := (ZMod.val_pos).mpr hx
  have hvN : x.val < N := ZMod.val_lt x
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hexp : (ZMod.stdAddChar x : ℂ) = exp (((2 * Real.pi * x.val / N : ℝ) : ℂ) * I) := by
    rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply]
    congr 1; push_cast; ring
  rw [hexp, arg_one_sub_exp]
  · ring
  · have : (0 : ℝ) < x.val := by exact_mod_cast hv
    positivity
  · rw [div_lt_iff₀ hN]
    have : (x.val : ℝ) < N := by exact_mod_cast hvN
    nlinarith [Real.pi_pos]

/-- **`B_{1,χ} ≠ 0`** for odd primitive Dirichlet characters, from `L(1, χ̄) ≠ 0`. -/
theorem Bsum_ne_zero {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (hodd : χ.Odd) :
    Bsum χ ≠ 0 := by
  -- basic facts
  have hN1 : N ≠ 1 := by
    rintro rfl
    have h := hodd
    unfold DirichletCharacter.Odd at h
    rw [show (-1 : ZMod 1) = 1 from rfl, map_one] at h
    norm_num at h
  have : Nontrivial (ZMod N) := ZMod.nontrivial_iff.mpr hN1
  have hχ1 : χ ≠ 1 := by
    rintro rfl
    have h := hodd
    unfold DirichletCharacter.Odd at h
    rw [MulChar.one_apply (isUnit_one.neg)] at h
    norm_num at h
  have hχi : χ⁻¹ ≠ 1 := fun h => hχ1 (inv_eq_one.mp h)
  have hτ0 : gaussSum χ ZMod.stdAddChar ≠ 0 := gaussSum_ne_zero_of_isPrimitive hχ
  -- the series for `τ L(1, χ⁻¹)`
  have hL := (tendsto_LFunction_one hχi).const_mul (gaussSum χ ZMod.stdAddChar)
  have hterm : ∀ n : ℕ, gaussSum χ ZMod.stdAddChar * (χ⁻¹ ((n + 1 : ℕ) : ZMod N) / ((n : ℂ) + 1)) =
      ∑ x, χ x * (ZMod.stdAddChar x ^ (n + 1) / ((n : ℂ) + 1)) := by
    intro n
    rw [mul_div_assoc', mul_comm, inv_mul_gaussSum hχ, sum_div]
    exact sum_congr rfl (fun x _ => by rw [mul_div_assoc])
  have hexpand : ∀ M, gaussSum χ ZMod.stdAddChar *
      ∑ n ∈ range M, χ⁻¹ ((n + 1 : ℕ) : ZMod N) / ((n : ℂ) + 1) =
      ∑ x, χ x * ∑ n ∈ range M, ZMod.stdAddChar x ^ (n + 1) / ((n : ℂ) + 1) := by
    intro M
    rw [mul_sum, sum_congr rfl (fun n _ => hterm n), sum_comm]
    exact sum_congr rfl (fun x _ => by rw [mul_sum])
  simp_rw [hexpand] at hL
  have hR : Tendsto (fun M => ∑ x, χ x *
      ∑ n ∈ range M, ZMod.stdAddChar x ^ (n + 1) / ((n : ℂ) + 1)) atTop
      (𝓝 (∑ x, χ x * -log (1 - ZMod.stdAddChar x))) := by
    refine tendsto_finsetSum _ (fun x _ => ?_)
    by_cases hx : x = 0
    · subst hx
      rw [MulChar.map_zero]
      simp only [zero_mul]
      exact tendsto_const_nhds
    · exact tendsto_const_nhds.mul (tendsto_log_series (norm_stdAddChar x) (stdAddChar_ne_one hx))
  have hval : gaussSum χ ZMod.stdAddChar * χ⁻¹.LFunction 1 =
      ∑ x, χ x * -log (1 - ZMod.stdAddChar x) := tendsto_nhds_unique hL hR
  -- the real parts cancel
  have hgneg : ∀ x : ZMod N, Real.log ‖1 - ZMod.stdAddChar (-x)‖ =
      Real.log ‖1 - ZMod.stdAddChar x‖ := by
    intro x
    congr 1
    have hw : (ZMod.stdAddChar x : ℂ) ≠ 0 := by
      intro h; have := norm_stdAddChar x; rw [h, norm_zero] at this; norm_num at this
    rw [AddChar.map_neg_eq_inv]
    have : (1 : ℂ) - (ZMod.stdAddChar x)⁻¹ = (ZMod.stdAddChar x - 1) * (ZMod.stdAddChar x)⁻¹ := by
      field_simp
    rw [this, norm_mul, norm_inv, norm_stdAddChar, inv_one, mul_one, norm_sub_rev]
  have hS : ∑ x, χ x * ((Real.log ‖1 - ZMod.stdAddChar x‖ : ℝ) : ℂ) = 0 := by
    have h1 : ∑ x, χ x * ((Real.log ‖1 - ZMod.stdAddChar x‖ : ℝ) : ℂ) =
        ∑ x, χ (-x) * ((Real.log ‖1 - ZMod.stdAddChar (-x)‖ : ℝ) : ℂ) :=
      (Fintype.sum_equiv (Equiv.neg (ZMod N)) _ _ (fun _ => rfl)).symm
    simp_rw [hgneg, hodd.eval_neg, neg_mul, sum_neg_distrib] at h1
    exact self_eq_neg.mp h1
  -- the imaginary parts give the Bernoulli sum
  have hA : ∑ x, χ x * (arg (1 - ZMod.stdAddChar x) : ℂ) = (Real.pi / N : ℂ) * Bsum χ := by
    have h1 : ∀ x, χ x * (arg (1 - ZMod.stdAddChar x) : ℂ) =
        (Real.pi / N : ℂ) * (χ x * (x.val : ℂ)) - (Real.pi / 2 : ℂ) * χ x := by
      intro x
      by_cases hx : x = 0
      · subst hx; rw [MulChar.map_zero]; simp
      · rw [arg_one_sub_stdAddChar hx]; push_cast; ring
    simp_rw [h1, sum_sub_distrib, ← mul_sum, MulChar.sum_eq_zero_of_ne_one hχ1, mul_zero,
      sub_zero, sum_eq_Bsum]
  have hlog : ∀ x : ZMod N, log (1 - ZMod.stdAddChar x) =
      ((Real.log ‖1 - ZMod.stdAddChar x‖ : ℝ) : ℂ) + (arg (1 - ZMod.stdAddChar x) : ℂ) * I := by
    intro x
    rw [← Complex.re_add_im (log (1 - ZMod.stdAddChar x)), log_re, log_im]
  have hfinal : gaussSum χ ZMod.stdAddChar * χ⁻¹.LFunction 1 =
      -(I * ((Real.pi / N : ℂ) * Bsum χ)) := by
    rw [hval]
    simp_rw [hlog, mul_neg, mul_add, sum_neg_distrib, sum_add_distrib, hS, zero_add]
    rw [← hA, mul_sum]
    congr 1
    exact sum_congr rfl (fun x _ => by ring)
  intro hB
  rw [hB, mul_zero, mul_zero, neg_zero] at hfinal
  exact DirichletCharacter.LFunction_apply_one_ne_zero hχi
    ((mul_eq_zero.mp hfinal).resolve_left hτ0)

/-- The hypothesis `BernoulliNV` holds. -/
theorem bernoulliNV : BernoulliNV := fun _ _ _ hχ hodd => Bsum_ne_zero hχ hodd

end gauss

section final

variable {m : ℕ} [NeZero m]

/-- **Hodge quadruples are decomposable**, with no hypothesis. -/
theorem quadruple' (hm2 : ¬2 ∣ m) (hm3 : ¬3 ∣ m) (A : Multiset (ZMod m))
    (hcard : Multiset.card A = 4) (hA : A.sum = 0) (h : ℕ)
    (hH : ∀ t : (ZMod m)ˣ, (A.map fun a => ((t : ZMod m) * a).val).sum = h) :
    ∃ a ∈ A, -a ∈ A :=
  quadruple hm2 hm3 bernoulliNV A hcard hA h hH

/-- **Hodge sextuples contain a pair or are `5`-standard**, with no hypothesis. -/
theorem sextuple' (hm2 : ¬2 ∣ m) (hm3 : ¬3 ∣ m) (A : Multiset (ZMod m))
    (hcard : Multiset.card A = 6) (hA : A.sum = 0) (h : ℕ)
    (hH : ∀ t : (ZMod m)ˣ, (A.map fun a => ((t : ZMod m) * a).val).sum = h) :
    (∃ a ∈ A, -a ∈ A) ∨ Std5 A :=
  sextuple hm2 hm3 bernoulliNV A hcard hA h hH

theorem hodge_quadruple' (hm2 : ¬2 ∣ m) (hm3 : ¬3 ∣ m) (α : Fin 4 → ZMod m) (hα : IsHodge α) :
    Decomposable α :=
  hodge_quadruple hm2 hm3 bernoulliNV α hα

theorem hodge_sextuple' (hm2 : ¬2 ∣ m) (hm3 : ¬3 ∣ m) (α : Fin 6 → ZMod m) (hα : IsHodge α) :
    Decomposable α ∨ Standard5 α :=
  hodge_sextuple hm2 hm3 bernoulliNV α hα

/-- **The Hodge conjecture for the Fermat fourfold of degree `m` prime to `6`**, relative only to
the geometric inputs (Shioda's description of the Hodge classes, the algebraicity of the
eigenclasses of decomposable characters, and Aoki's cycles for the `5`-standard ones). -/
theorem hodge_fermat_fourfold' (hm2 : ¬2 ∣ m) (hm3 : ¬3 ∣ m)
    (Alg : (Fin 6 → ZMod m) → Prop)
    (hdec : ∀ α, IsHodge α → Decomposable α → Alg α)
    (hstd : ∀ α, IsHodge α → Standard5 α → Alg α) :
    ∀ α, IsHodge α → Alg α :=
  hodge_fermat_fourfold hm2 hm3 bernoulliNV Alg hdec hstd

end final

end FermatHodge
