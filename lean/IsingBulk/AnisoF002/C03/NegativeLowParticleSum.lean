import IsingBulk.AnisoF002.C03.NegativeBoundaryJets
import IsingBulk.AnisoF002.C03.NegativeHighParticleThreshold

/-!
# The complete physical low-particle Taylor sum

The coefficient here is the factorial-normalized derivative of the literal
physical real-cycle coefficient.  All nonasymptotic odd populations are
included.  The finite range is exactly `2n+1 ≤ log j`.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open Set Filter
open scoped Topology BigOperators

def physicalOddTaylorCoefficient (b B : ℂ → ℂ) (φ : ℝ) (j n : ℕ) : ℂ :=
  iteratedDeriv j (negativePhysicalCoefficient b B φ (2 * n)) 0 / (j.factorial : ℂ)

theorem exists_actual_odd_taylor_majorant {b B : ℂ → ℂ} {φ : ℝ}
    (hb : AnalyticAt ℂ b 0) (hB : AnalyticAt ℂ B 0)
    (hφ : 0 < φ) (hπ : φ < Real.pi) (hBi : (B 0).im < 0)
    (hbsq : ∀ t, b t ^ 2 = B t) :
    ∃ M c kappa : ℝ, 0 < M ∧ 0 < c ∧ 0 < kappa ∧
      ∀ j n : ℕ, ‖physicalOddTaylorCoefficient b B φ j n‖ ≤
        (M / c ^ j) * ((2 * n + 1 : ℕ) : ℝ) ^ (2 * j + 1) *
          Real.exp (-kappa * ((2 * n + 1 : ℕ) : ℝ) ^ 2) := by
  obtain ⟨d⟩ := exists_negative_coefficient_control hB hφ hπ hBi
  obtain ⟨M, kappa, hM, hk, hbound⟩ := d.exists_coefficient_uniform_jets
  obtain ⟨ζ, _, hζ, he⟩ := eventually_physical_odd_coefficients φ hb hB hBi hbsq
  refine ⟨M, d.coefficientConstant, kappa, hM, d.coefficientConstant_pos, hk, ?_⟩
  intro j n
  have heq : negativePhysicalCoefficient b B φ (2 * n) =ᶠ[𝓝 0]
      (fun t => ζ * negativeCanonicalCoefficient B φ (2 * n) t) :=
    he.mono fun t ht => ht (2 * n) ⟨n, rfl⟩
  have hnorm : ‖iteratedDeriv j (negativePhysicalCoefficient b B φ (2 * n)) 0‖ =
      ‖iteratedDeriv j (negativeCanonicalCoefficient B φ (2 * n)) 0‖ := by
    rw [heq.iteratedDeriv_eq j, iteratedDeriv_const_mul_field, norm_mul, hζ, one_mul]
  have hh := hbound j (2 * n) ⟨n, rfl⟩ 0 le_rfl d.eps0_pos.le
  simp only [Complex.ofReal_zero, neg_zero] at hh
  unfold physicalOddTaylorCoefficient
  rw [norm_div, norm_natCast, hnorm]
  apply (div_le_iff₀ (by exact_mod_cast j.factorial_pos : (0 : ℝ) < j.factorial)).mpr
  convert hh using 1
  ring

def lowOddParticleIndices (j : ℕ) : Finset ℕ :=
  (Finset.range (j + 1)).filter (fun n => ((2 * n + 1 : ℕ) : ℝ) ≤ Real.log (j : ℝ))

theorem mem_lowOddParticleIndices {j n : ℕ} (hj : 0 < j) :
    n ∈ lowOddParticleIndices j ↔ ((2 * n + 1 : ℕ) : ℝ) ≤ Real.log (j : ℝ) := by
  rw [lowOddParticleIndices, Finset.mem_filter]
  constructor
  · exact And.right
  · intro hn
    refine ⟨Finset.mem_range.mpr ?_, hn⟩
    have hjr : (0 : ℝ) < j := by exact_mod_cast hj
    have hl := Real.log_le_sub_one_of_pos hjr
    have hnj : (n : ℝ) ≤ (j : ℝ) := by push_cast at hn; nlinarith
    have : n ≤ j := by exact_mod_cast hnj
    omega

theorem low_odd_majorant_pointwise {j n : ℕ} {M c kappa : ℝ}
    (hM : 0 < M) (hc : 0 < c) (hk : 0 ≤ kappa)
    (hj : 0 < j) (hn : ((2 * n + 1 : ℕ) : ℝ) ≤ Real.log (j : ℝ)) :
    (M / c ^ j) * ((2 * n + 1 : ℕ) : ℝ) ^ (2 * j + 1) *
        Real.exp (-kappa * ((2 * n + 1 : ℕ) : ℝ) ^ 2) ≤
      Real.exp (2 * (j : ℝ) * Real.log (Real.log (j : ℝ)) +
        (|Real.log c| + 1) * (j : ℝ) + |Real.log M|) := by
  have hN : (0 : ℝ) < ((2 * n + 1 : ℕ) : ℝ) := by positivity
  have hjr : (0 : ℝ) < j := by exact_mod_cast hj
  have hlog : Real.log ((2 * n + 1 : ℕ) : ℝ) ≤ Real.log (Real.log (j : ℝ)) :=
    Real.log_le_log hN hn
  have hlogextra : Real.log ((2 * n + 1 : ℕ) : ℝ) ≤ (j : ℝ) := by
    have h1 := Real.log_le_sub_one_of_pos hN
    have h2 := Real.log_le_sub_one_of_pos hjr
    linarith
  have hgauss : Real.exp (-kappa * ((2 * n + 1 : ℕ) : ℝ) ^ 2) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hk) (sq_nonneg _)
  calc
    _ ≤ (M / c ^ j) * ((2 * n + 1 : ℕ) : ℝ) ^ (2 * j + 1) := by
      nlinarith [mul_le_mul_of_nonneg_left hgauss
        (show 0 ≤ (M / c ^ j) * ((2 * n + 1 : ℕ) : ℝ) ^ (2 * j + 1) by positivity)]
    _ ≤ _ := by
      apply (Real.log_le_iff_le_exp (by positivity)).mp
      rw [Real.log_mul (by positivity) (by positivity),
        Real.log_div hM.ne' (pow_pos hc _).ne', Real.log_pow, Real.log_pow]
      have hmain := mul_le_mul_of_nonneg_left hlog (show (0 : ℝ) ≤ 2 * j by positivity)
      have hcabs := mul_le_mul_of_nonneg_left (neg_le_abs (Real.log c)) hjr.le
      have hMabs := le_abs_self (Real.log M)
      push_cast at hmain hlogextra ⊢
      nlinarith

theorem complete_low_odd_majorant_bound {M c kappa : ℝ}
    (hM : 0 < M) (hc : 0 < c) (hk : 0 ≤ kappa) :
    ∃ A : ℝ, 0 < A ∧ ∀ j : ℕ, 0 < j →
      (∑ n ∈ lowOddParticleIndices j,
        (M / c ^ j) * ((2 * n + 1 : ℕ) : ℝ) ^ (2 * j + 1) *
          Real.exp (-kappa * ((2 * n + 1 : ℕ) : ℝ) ^ 2)) ≤
        Real.exp (2 * (j : ℝ) * Real.log (Real.log (j : ℝ)) + A * j + A) := by
  let A : ℝ := |Real.log c| + |Real.log M| + 3
  refine ⟨A, by dsimp [A]; positivity, ?_⟩
  intro j hj
  let E : ℝ := 2 * (j : ℝ) * Real.log (Real.log (j : ℝ)) +
    (|Real.log c| + 1) * (j : ℝ) + |Real.log M|
  have hsum : (∑ n ∈ lowOddParticleIndices j,
      (M / c ^ j) * ((2 * n + 1 : ℕ) : ℝ) ^ (2 * j + 1) *
        Real.exp (-kappa * ((2 * n + 1 : ℕ) : ℝ) ^ 2)) ≤
      ((lowOddParticleIndices j).card : ℝ) * Real.exp E := by
    calc
      _ ≤ ∑ _n ∈ lowOddParticleIndices j, Real.exp E := by
        apply Finset.sum_le_sum
        intro n hn
        exact low_odd_majorant_pointwise hM hc hk hj ((mem_lowOddParticleIndices hj).mp hn)
      _ = _ := by simp
  have hcard : ((lowOddParticleIndices j).card : ℝ) ≤ (j : ℝ) + 1 := by
    have hh := Finset.card_le_card (Finset.filter_subset
      (fun n => ((2 * n + 1 : ℕ) : ℝ) ≤ Real.log (j : ℝ)) (Finset.range (j + 1)))
    simp only [Finset.card_range] at hh
    simpa only [lowOddParticleIndices, Finset.card_range, Nat.cast_add, Nat.cast_one]
      using (show (((Finset.range (j + 1)).filter
        (fun n => ((2 * n + 1 : ℕ) : ℝ) ≤ Real.log (j : ℝ))).card : ℝ) ≤
          ((j + 1 : ℕ) : ℝ) by exact_mod_cast hh)
  have hcount : ((lowOddParticleIndices j).card : ℝ) ≤ Real.exp ((j : ℝ) + 1) := by
    have hh := Real.add_one_le_exp ((j : ℝ) + 1)
    linarith
  apply hsum.trans
  apply (mul_le_mul_of_nonneg_right hcount (Real.exp_pos E).le).trans
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  dsimp [A, E]
  nlinarith [abs_nonneg (Real.log c), abs_nonneg (Real.log M), Nat.cast_nonneg (α := ℝ) j]

theorem exists_actual_complete_low_particle_bound {b B : ℂ → ℂ} {φ : ℝ}
    (hb : AnalyticAt ℂ b 0) (hB : AnalyticAt ℂ B 0)
    (hφ : 0 < φ) (hπ : φ < Real.pi) (hBi : (B 0).im < 0)
    (hbsq : ∀ t, b t ^ 2 = B t) :
    ∃ A : ℝ, 0 < A ∧ ∀ j : ℕ, 0 < j →
      (∑ n ∈ lowOddParticleIndices j, ‖physicalOddTaylorCoefficient b B φ j n‖) ≤
        Real.exp (2 * (j : ℝ) * Real.log (Real.log (j : ℝ)) + A * j + A) := by
  obtain ⟨M, c, kappa, hM, hc, hk, hbnd⟩ :=
    exists_actual_odd_taylor_majorant hb hB hφ hπ hBi hbsq
  obtain ⟨A, hA, hsum⟩ := complete_low_odd_majorant_bound hM hc hk.le
  refine ⟨A, hA, ?_⟩
  intro j hj
  exact (Finset.sum_le_sum (fun n _ => hbnd j n)).trans (hsum j hj)

end
end IsingBulk.AnisoF002.NegativeHT
