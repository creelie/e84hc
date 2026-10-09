import FermatHodge.Kill

/-!
# From characters to the slice condition

If `F : (ZMod e)ˣ → ℤ` is orthogonal to every primitive Dirichlet character mod `e`, then
`SIAt Ks F x` holds for every list `Ks` containing all the subgroups `K_p`.  The proof expands
`F` in characters: a character that is not primitive is trivial on some `K_p`, and iterated
differences along subgroups only rescale a character, so they vanish once they reach that `K_p`.
-/

open Finset

noncomputable section

namespace FermatHodge

open Classical

set_option linter.unusedSectionVars false

section general

variable {G : Type*} [CommGroup G] [Fintype G]

/-- `SIAt` for complex-valued functions. -/
def SIAtC : List (Subgroup G) → (G → ℂ) → G → Prop
  | [], f, x => f x = 0
  | K :: Ks, f, x => ∀ c ∈ K, ∀ k ∈ K, SIAtC Ks (fun z => f z - f (z * k)) (x * c)

lemma SIAt_iff_SIAtC : ∀ (Ks : List (Subgroup G)) (f : G → ℤ) (x : G),
    SIAt Ks f x ↔ SIAtC Ks (fun z => (f z : ℂ)) x
  | [], f, x => by simp [SIAt, SIAtC]
  | K :: Ks, f, x => by
      simp only [SIAt, SIAtC]
      refine forall₂_congr fun c _ => forall₂_congr fun k _ => ?_
      rw [SIAt_iff_SIAtC Ks]
      simp only [Int.cast_sub]

lemma SIAtC_congr {Ks : List (Subgroup G)} {f g : G → ℂ} {x : G} (h : ∀ z, f z = g z)
    (hf : SIAtC Ks f x) : SIAtC Ks g x := by
  have : f = g := funext h
  rwa [← this]

lemma SIAtC_zero : ∀ (Ks : List (Subgroup G)) (x : G), SIAtC Ks (fun _ => 0) x
  | [], x => by simp [SIAtC]
  | K :: Ks, x => by
      intro c _ k _
      exact SIAtC_congr (fun z => by simp) (SIAtC_zero Ks _)

lemma SIAtC_add : ∀ (Ks : List (Subgroup G)) (f g : G → ℂ) (x : G),
    SIAtC Ks f x → SIAtC Ks g x → SIAtC Ks (fun z => f z + g z) x
  | [], f, g, x, hf, hg => by simp only [SIAtC] at *; rw [hf, hg, add_zero]
  | K :: Ks, f, g, x, hf, hg => by
      intro c hc k hk
      exact SIAtC_congr (fun z => by ring)
        (SIAtC_add Ks _ _ (x * c) (hf c hc k hk) (hg c hc k hk))

lemma SIAtC_smul : ∀ (Ks : List (Subgroup G)) (a : ℂ) (f : G → ℂ) (x : G),
    SIAtC Ks f x → SIAtC Ks (fun z => a * f z) x
  | [], a, f, x, hf => by simp only [SIAtC] at *; rw [hf, mul_zero]
  | K :: Ks, a, f, x, hf => by
      intro c hc k hk
      exact SIAtC_congr (fun z => by ring) (SIAtC_smul Ks a _ (x * c) (hf c hc k hk))

lemma SIAtC_sum {ι : Type*} (s : Finset ι) (Ks : List (Subgroup G)) (f : ι → G → ℂ) (x : G)
    (h : ∀ i ∈ s, SIAtC Ks (f i) x) : SIAtC Ks (fun z => ∑ i ∈ s, f i z) x := by
  induction s using Finset.induction_on with
  | empty => exact SIAtC_congr (fun z => by simp) (SIAtC_zero Ks x)
  | insert i s hi ih =>
      refine SIAtC_congr (fun z => (Finset.sum_insert hi).symm)
        (SIAtC_add Ks _ _ x (h i (mem_insert_self i s)) (ih fun j hj => h j (mem_insert_of_mem hj)))

/-- A multiple of a character that is trivial on one of the subgroups. -/
lemma SIAtC_char (χ : G →* ℂ) : ∀ (Ks : List (Subgroup G)) (a : ℂ) (x : G),
    (∃ K ∈ Ks, ∀ k ∈ K, χ k = 1) → SIAtC Ks (fun z => a * χ z) x
  | [], _, _, ⟨K, hK, _⟩ => by simp at hK
  | L :: Ks, a, x, ⟨K, hK, hχ⟩ => by
      intro c _ k hk
      rcases List.mem_cons.mp hK with rfl | hK
      · refine SIAtC_congr (fun z => ?_) (SIAtC_zero Ks (x * c))
        simp only; rw [map_mul, hχ k hk]; ring
      · refine SIAtC_congr (fun z => ?_) (SIAtC_char χ Ks (a * (1 - χ k)) (x * c) ⟨K, hK, hχ⟩)
        simp only; rw [map_mul]; ring

end general

section dirichlet

variable {e : ℕ} [NeZero e]

/-- A Dirichlet character as a homomorphism from the units to `ℂ`. -/
def chiHom (χ : DirichletCharacter ℂ e) : (ZMod e)ˣ →* ℂ := (Units.coeHom ℂ).comp χ.toUnitHom

lemma chiHom_apply (χ : DirichletCharacter ℂ e) (z : (ZMod e)ˣ) : chiHom χ z = χ z := by
  simp [chiHom]

/-- Fourier inversion on `(ZMod e)ˣ`. -/
lemma fourier (F : (ZMod e)ˣ → ℂ) (z : (ZMod e)ˣ) :
    (e.totient : ℂ) * F z =
      ∑ χ : DirichletCharacter ℂ e, (∑ w, F w * χ ((w : ZMod e)⁻¹)) * χ z := by
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  have h : ∀ w : (ZMod e)ˣ, ∑ χ : DirichletCharacter ℂ e, F w * χ ((w : ZMod e)⁻¹) * χ z =
      if w = z then F z * e.totient else 0 := by
    intro w
    simp_rw [mul_assoc, ← Finset.mul_sum]
    rw [DirichletCharacter.sum_char_inv_mul_char_eq ℂ w.isUnit (z : ZMod e)]
    by_cases hw : w = z
    · subst hw; simp
    · have : (w : ZMod e) ≠ z := fun h => hw (Units.ext h)
      simp [this, hw]
  rw [Finset.sum_congr rfl (fun w _ => h w), Finset.sum_ite_eq' univ z, if_pos (mem_univ z),
    mul_comm]

/-- A character that is not primitive is trivial on some `K_p`. -/
lemma exists_Kq_trivial (χ : DirichletCharacter ℂ e) (hχ : ¬χ.IsPrimitive) :
    ∃ p, p.Prime ∧ p ∣ e ∧ ∀ k ∈ Kq e p, χ k = 1 := by
  set c := χ.conductor with hcdef
  have hce : c ∣ e := χ.conductor_dvd_level
  have hne : c ≠ e := hχ
  have he0 : e ≠ 0 := NeZero.ne e
  obtain ⟨r, hr⟩ := hce
  have hr1 : r ≠ 1 := by rintro rfl; exact hne (by rw [hr, mul_one])
  set p := r.minFac
  have hp : p.Prime := Nat.minFac_prime hr1
  obtain ⟨q, hq⟩ := Nat.minFac_dvd r
  have hpe : p ∣ e := ⟨c * q, by rw [hr, hq]; ring⟩
  have hdiv : e / p = c * q := by
    rw [hr, hq, show c * (p * q) = p * (c * q) by ring, Nat.mul_div_cancel_left _ hp.pos]
  have hcd : c ∣ e / p := ⟨q, hdiv⟩
  refine ⟨p, hp, hpe, fun k hk => ?_⟩
  have hft := DirichletCharacter.FactorsThrough.mono χ χ.factorsThrough_conductor hcd
    (Nat.div_dvd_of_dvd hpe)
  have hker := (DirichletCharacter.factorsThrough_iff_ker_unitsMap (Nat.div_dvd_of_dvd hpe)).mp hft
  rw [Kq_of_dvd hpe, Nd] at hk
  have := hker hk
  rw [MonoidHom.mem_ker] at this
  rw [← MulChar.coe_toUnitHom, this, Units.val_one]

/-- Orthogonality to all primitive characters gives the slice condition. -/
theorem SIAt_of_fourier (F : (ZMod e)ˣ → ℤ)
    (hF : ∀ χ : DirichletCharacter ℂ e, χ.IsPrimitive →
      ∑ w, (F w : ℂ) * χ ((w : ZMod e)⁻¹) = 0)
    (Ks : List (Subgroup (ZMod e)ˣ)) (hKs : ∀ p, p.Prime → p ∣ e → Kq e p ∈ Ks)
    (x : (ZMod e)ˣ) : SIAt Ks F x := by
  rw [SIAt_iff_SIAtC]
  have htot : (e.totient : ℂ) ≠ 0 := by
    have := Nat.totient_pos.2 (Nat.pos_of_ne_zero (NeZero.ne e))
    exact_mod_cast this.ne'
  have h1 : SIAtC Ks (fun z => (e.totient : ℂ) * (F z : ℂ)) x := by
    refine SIAtC_congr (fun z => (fourier (fun w => (F w : ℂ)) z).symm) ?_
    refine SIAtC_sum univ Ks _ x (fun χ _ => ?_)
    by_cases hχ : χ.IsPrimitive
    · refine SIAtC_congr (fun z => ?_) (SIAtC_zero Ks x)
      show (0 : ℂ) = (∑ w, (F w : ℂ) * χ ((w : ZMod e)⁻¹)) * χ z
      rw [hF χ hχ, zero_mul]
    · obtain ⟨p, hp, hpe, htriv⟩ := exists_Kq_trivial χ hχ
      refine SIAtC_congr (fun z => by rw [chiHom_apply]) (SIAtC_char (chiHom χ) Ks _ x
        ⟨Kq e p, hKs p hp hpe, fun k hk => by rw [chiHom_apply]; exact htriv k hk⟩)
  refine SIAtC_congr (fun z => ?_) (SIAtC_smul Ks ((e.totient : ℂ)⁻¹) _ x h1)
  show (e.totient : ℂ)⁻¹ * ((e.totient : ℂ) * (F z : ℂ)) = (F z : ℂ)
  rw [← mul_assoc, inv_mul_cancel₀ htot, one_mul]

end dirichlet

end FermatHodge
