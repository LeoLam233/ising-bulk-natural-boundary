import IsingBulk.AnisoF002.C03.RegularParticleHighSum
import IsingBulk.AnisoF002.C03.RegularWindingPhysicalSectorIdentity
import IsingBulk.AnisoF002.C03.NegativeWindingHighParticle
import IsingBulk.AnisoF002.C03.NegativeFullTaylorExtraction

/-!
# The complete actual physical high-particle residue tail

The all-winding estimate is applied to the exact physical coefficient.
The finite radius restrictions disappear above the actual high cutoff
for large Taylor order.  Both the cutoff and the exponential constant
are chosen from the original physical analytic data before the family
of particles or the order.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open Filter
open scoped Topology BigOperators Classical

theorem sqrt_order_le_highParticleThreshold {j : ℕ} (hj : 0 < j)
    (hlog : 0 < Real.log (j : ℝ)) :
    Real.sqrt (j : ℝ) ≤ highParticleThreshold j := by
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
  have hjlog := Real.log_le_sub_one_of_pos hj0
  have hsqrtlog : Real.sqrt (Real.log (j : ℝ)) ≤ Real.sqrt (j : ℝ) :=
    Real.sqrt_le_sqrt (by linarith)
  have hsqrtj := Real.sqrt_nonneg (j : ℝ)
  unfold highParticleThreshold
  apply (le_div_iff₀ (Real.sqrt_pos.mpr hlog)).mpr
  nlinarith [Real.sq_sqrt hj0.le]

theorem eventually_highParticleThreshold_ge (L : ℝ) :
    ∀ᶠ j : ℕ in atTop, L ≤ highParticleThreshold j := by
  have hlog : Tendsto (fun j : ℕ => Real.log (j : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlog.eventually (eventually_ge_atTop 1),
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
      (eventually_ge_atTop ((max L 1) ^ 2))] with j hjlog hjlarge
  have hj : 0 < j := by
    by_contra hn
    have hz : j = 0 := by omega
    norm_num [hz] at hjlog
  have hmax : 0 < max L 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hroot : max L 1 ≤ Real.sqrt (j : ℝ) := by
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) j), Real.sqrt_nonneg (j : ℝ)]
  exact (le_max_left _ _).trans (hroot.trans (sqrt_order_le_highParticleThreshold hj (by linarith)))

theorem eventually_high_particle_radius {R : ℝ} (hR : 0 < R) (r : ℝ) :
    ∀ᶠ j : ℕ in atTop, ∀ N : ℕ, highParticleThreshold j < (N : ℝ) ^ 2 →
      2 < N ∧ r / (4 * (N : ℝ)) ≤ R := by
  let V : ℝ := max 2 (|r| / (4 * R))
  have hV2 : 2 ≤ V := le_max_left _ _
  have hVr : |r| ≤ 4 * R * V := by
    have h := (div_le_iff₀ (by positivity : 0 < 4 * R)).mp
      (show |r| / (4 * R) ≤ V from le_max_right _ _)
    nlinarith
  filter_upwards [eventually_highParticleThreshold_ge (V ^ 2)] with j hj
  intro N hN
  have hVN : V < (N : ℝ) := by
    nlinarith [Nat.cast_nonneg (α := ℝ) N]
  have hN2 : (2 : ℝ) < N := hV2.trans_lt hVN
  refine ⟨by exact_mod_cast hN2, ?_⟩
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 4 * N)).mpr
  have hmul := mul_le_mul_of_nonneg_left hVN.le (show 0 ≤ 4 * R by positivity)
  nlinarith [le_abs_self r]

theorem exists_actual_complete_high_particle_bound {b B : ℂ → ℂ} {φ : ℝ}
    (hb : AnalyticAt ℂ b 0) (hB : AnalyticAt ℂ B 0)
    (hφ : 0 < φ) (hπ : φ < Real.pi) (hBi : (B 0).im < 0)
    (hbsq : ∀ t, b t ^ 2 = B t) :
    ∃ s0 A : ℝ, 0 < s0 ∧ 0 < A ∧
      ∀ r s Mi ki : ℝ, 0 < r → 0 < s → 0 ≤ Mi → s ≤ s0 →
      ∀ D : ∀ n : ℕ, InnerRemainderFamily b B φ (2 * n + 1) r s Mi ki,
      ∀ᶠ j : ℕ in atTop,
        Summable (fun n : ℕ => if highParticleThreshold j < ((2 * n + 1 : ℕ) : ℝ) ^ 2
          then ‖completeCyclePoleCoefficient D j n‖ else 0) ∧
        (∑' n : ℕ, if highParticleThreshold j < ((2 * n + 1 : ℕ) : ℝ) ^ 2
          then ‖completeCyclePoleCoefficient D j n‖ else 0) ≤ Real.exp (completeHighExponent A j) := by
  obtain ⟨c⟩ := exists_physical_winding_residue_control hb hB hφ hπ hBi hbsq
  obtain ⟨R, sid, hR, hsid, hid⟩ := exists_actual_winding_sector_identity_radii hb hB hφ hπ hBi hbsq
  obtain ⟨C, hC, hbound⟩ := c.exists_complete_high_particle_residue_bound hφ hπ
  obtain ⟨A, hA, hsum⟩ := exists_complete_high_subsequence_bound hC.le
  let s0 := min c.cutoff sid
  refine ⟨s0, A, lt_min c.cutoff_pos hsid, hA, ?_⟩
  intro r s Mi ki hr hs hMi hss0 D
  have hsc : s ≤ c.cutoff := hss0.trans (min_le_left _ _)
  have hsid' : s ≤ sid := hss0.trans (min_le_right _ _)
  have hlog : Tendsto (fun j : ℕ => Real.log (j : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_high_particle_radius (lt_min hR c.radius_pos) r,
    hlog.eventually (eventually_ge_atTop 256),
    hlog.eventually (eventually_ge_atTop (16 * (C + 1))),
    eventually_ge_atTop 1] with j hjrad hjlog hjC hj
  apply hsum j hj hjlog hjC (fun n => 2 * n + 1) (by intro m n hmn; dsimp at hmn; omega)
    (fun n => ‖completeCyclePoleCoefficient D j n‖) (fun _ => norm_nonneg _)
  intro n hn
  obtain ⟨hN, hrad⟩ := hjrad (2 * n + 1) hn
  have hradR : r / (4 * ((2 * n + 1 : ℕ) : ℝ)) ≤ R := hrad.trans (min_le_left _ _)
  have hradc : r / (4 * ((2 * n + 1 : ℕ) : ℝ)) ≤ c.radius := hrad.trans (min_le_right _ _)
  by_cases hres : Complex.exp (-(((2 * n + 1 : ℕ) : ℂ) * ((φ : ℂ) * Complex.I))) = 1
  · rw [completeCyclePoleCoefficient, ite_eq_left hres,
      hid (2 * n) ⟨n, rfl⟩ r s Mi ki (D n) hr hs.le hMi hsid' hradR hres j]
    apply (norm_sum_le _ _).trans
    exact hbound r s Mi ki (2 * n) (D n) (by omega) hs hsc hradc j
  · simp only [completeCyclePoleCoefficient, hres, ↓reduceIte, norm_zero]
    positivity

end
end IsingBulk.AnisoF002.NegativeHT
