import IsingBulk.AnisoF002.RegularTail.VandermondeBlock
import IsingBulk.AnisoF002.RegularTail.CollisionBudget
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass

/-!
# The actual fixed-dimensional angular collision majorant is integrable

The retained sine product is bounded in the finite-coordinate supremum
norm.  The quadratic angular sum dominates that norm squared.  Haar
integrability of the resulting radial power proves integrability in the
actual m independent real coordinates, with the exact threshold m²>2p.
This is a multidimensional majorant theorem, not just a one-dimensional
radial model calculation.
-/

namespace IsingBulk.AnisoF002.RegularTail.C03
noncomputable section
open Set MeasureTheory IsingBulk.AnisoF002.Isotropic
open scoped BigOperators Topology

def angularQuadratic {m : ℕ} (x : Fin m → ℝ) : ℝ := ∑ i, x i ^ 2

def retainedBlockPole {m : ℕ} (p : ℕ) (x : Fin m → ℝ) : ℝ :=
  retainedSineBlock x / angularQuadratic x ^ p

def retainedCollisionMajorant {m : ℕ} (kappa : ℝ) (p : ℕ) (x : Fin m → ℝ) : ℝ :=
  retainedSineBlock x / min 1 (kappa * angularQuadratic x) ^ p

def regularAngularBox (m : ℕ) : Set (Fin m → ℝ) := Icc (fun _ => -Real.pi) (fun _ => Real.pi)

theorem regularAngularBox_compact (m : ℕ) : IsCompact (regularAngularBox m) := isCompact_Icc

theorem retainedSineBlock_nonneg {m : ℕ} (x : Fin m → ℝ) : 0 ≤ retainedSineBlock x :=
  Finset.prod_nonneg fun _ _ => sq_nonneg _

theorem retainedSineBlock_continuous (m : ℕ) : Continuous (retainedSineBlock : (Fin m → ℝ) → ℝ) := by
  unfold retainedSineBlock
  fun_prop

theorem angularQuadratic_nonneg {m : ℕ} (x : Fin m → ℝ) : 0 ≤ angularQuadratic x :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem angularQuadratic_continuous (m : ℕ) : Continuous (angularQuadratic : (Fin m → ℝ) → ℝ) := by
  unfold angularQuadratic
  fun_prop

theorem norm_square_le_angularQuadratic {m : ℕ} (x : Fin m → ℝ) :
    ‖x‖ ^ 2 ≤ angularQuadratic x := by
  have hnorm : ‖x‖ ≤ Real.sqrt (angularQuadratic x) := by
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
    intro i
    rw [Real.norm_eq_abs]
    exact Real.abs_le_sqrt (coordinate_square_le_sum x i)
  have hs := pow_le_pow_left₀ (norm_nonneg x) hnorm 2
  rwa [Real.sq_sqrt (angularQuadratic_nonneg x)] at hs

theorem angularQuadratic_pos_of_ne_zero {m : ℕ} {x : Fin m → ℝ} (hx : x ≠ 0) :
    0 < angularQuadratic x :=
  lt_of_lt_of_le (sq_pos_of_pos (norm_pos_iff.mpr hx)) (norm_square_le_angularQuadratic x)

theorem retainedSineBlock_norm_bound {m : ℕ} (x : Fin m → ℝ) :
    retainedSineBlock x ≤ ‖x‖ ^ (2 * m.choose 2) := by
  calc
    retainedSineBlock x ≤ ∏ _ij ∈ indexPairs m, ‖x‖ ^ 2 := by
      apply Finset.prod_le_prod₀ (fun _ _ => sq_nonneg _)
      intro ij _
      have hi : |x ij.1| ≤ ‖x‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm x ij.1
      have hj : |x ij.2| ≤ ‖x‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm x ij.2
      have hd : |(x ij.1 - x ij.2) / 2| ≤ ‖x‖ := by
        rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
        have ha := norm_sub_le (x ij.1) (x ij.2)
        simp only [Real.norm_eq_abs] at ha
        linarith
      have hs := pow_le_pow_left₀ (abs_nonneg ((x ij.1 - x ij.2) / 2)) hd 2
      rw [sq_abs] at hs
      exact Real.sin_sq_le_sq.trans hs
    _ = ‖x‖ ^ (2 * m.choose 2) := by
      rw [Finset.prod_const, card_indexPairs, ← pow_mul]

theorem retainedBlockPole_norm_bound {m p : ℕ} {x : Fin m → ℝ} (hx : x ≠ 0) :
    ‖retainedBlockPole p x‖ ≤
      ‖x‖ ^ ((2 * m.choose 2 : ℕ) : ℝ) / ‖x‖ ^ (2 * (p : ℝ)) := by
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hQ : 0 < angularQuadratic x := angularQuadratic_pos_of_ne_zero hx
  have hnonneg : 0 ≤ retainedBlockPole p x := div_nonneg (retainedSineBlock_nonneg x)
    (pow_nonneg hQ.le p)
  rw [Real.norm_of_nonneg hnonneg]
  calc
    retainedBlockPole p x ≤ ‖x‖ ^ (2 * m.choose 2) / (‖x‖ ^ 2) ^ p := by
      exact div_le_div₀ (pow_nonneg (norm_nonneg x) _) (retainedSineBlock_norm_bound x)
        (pow_pos (sq_pos_of_pos hn) p)
        (pow_le_pow_left₀ (sq_nonneg _) (norm_square_le_angularQuadratic x) p)
    _ = ‖x‖ ^ ((2 * m.choose 2 : ℕ) : ℝ) / ‖x‖ ^ (2 * (p : ℝ)) := by
      rw [Real.rpow_natCast,
        show 2 * (p : ℝ) = ((2 * p : ℕ) : ℝ) by push_cast; rfl,
        Real.rpow_natCast]
      simp only [pow_mul]

/-- Integrability of the actual retained sine product times the angular
pole in m independent coordinates, at the complete printed threshold. -/
theorem retainedBlockPole_locallyIntegrable {m p : ℕ}
    (hm : 0 < m) (hbudget : 2 * p < m ^ 2) :
    LocallyIntegrable (retainedBlockPole (m := m) p) volume := by
  let : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  have hdim : Module.finrank ℝ (Fin m → ℝ) = m := by simp
  have hdegree : ((2 * m.choose 2 : ℕ) : ℝ) = (m : ℝ) ^ 2 - m := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using vandermonde_degree m
  have hb : 2 * (p : ℝ) < (m : ℝ) ^ 2 := by exact_mod_cast hbudget
  have hα : 2 * (p : ℝ) - ((2 * m.choose 2 : ℕ) : ℝ) < Module.finrank ℝ (Fin m → ℝ) := by
    rw [hdim, hdegree]
    linarith
  have hmeas : Measurable (retainedBlockPole (m := m) p) :=
    (retainedSineBlock_continuous m).measurable.div ((angularQuadratic_continuous m).measurable.pow_const p)
  apply locallyIntegrable_of_norm_le_rpow (C := 1)
    (α := 2 * (p : ℝ) - ((2 * m.choose 2 : ℕ) : ℝ))
    (by rw [hdim]; exact hm) hα _ hmeas.aestronglyMeasurable
  filter_upwards [volume.ae_ne (0 : Fin m → ℝ)] with x hx
  have hbnd := retainedBlockPole_norm_bound (p := p) hx
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  simpa only [one_mul, ← Real.rpow_sub hn, neg_sub] using hbnd

theorem retainedCollisionMajorant_nonneg {m p : ℕ} {kappa : ℝ} (hk : 0 ≤ kappa)
    (x : Fin m → ℝ) : 0 ≤ retainedCollisionMajorant kappa p x := by
  exact div_nonneg (retainedSineBlock_nonneg x)
    (pow_nonneg (le_min (by norm_num) (mul_nonneg hk (angularQuadratic_nonneg x))) p)

theorem retainedCollisionMajorant_le {m p : ℕ} {kappa : ℝ} (hk : 0 < kappa)
    (x : Fin m → ℝ) :
    retainedCollisionMajorant kappa p x ≤
      retainedSineBlock x + (1 / kappa ^ p) * retainedBlockPole p x := by
  have hv := retainedSineBlock_nonneg x
  have hf : 0 ≤ retainedBlockPole p x := div_nonneg hv (pow_nonneg (angularQuadratic_nonneg x) p)
  by_cases h : 1 ≤ kappa * angularQuadratic x
  · simp only [retainedCollisionMajorant, min_eq_left h, one_pow, div_one]
    exact le_add_of_nonneg_right (mul_nonneg (by positivity) hf)
  · have hm : min 1 (kappa * angularQuadratic x) = kappa * angularQuadratic x := min_eq_right (le_of_not_ge h)
    have he : retainedCollisionMajorant kappa p x = (1 / kappa ^ p) * retainedBlockPole p x := by
      unfold retainedCollisionMajorant retainedBlockPole
      rw [hm, mul_pow, div_eq_mul_inv, mul_inv_rev]
      ring
    rw [he]
    exact le_add_of_nonneg_left hv

theorem retainedCollisionMajorant_locallyIntegrable {m p : ℕ} {kappa : ℝ}
    (hm : 0 < m) (hbudget : 2 * p < m ^ 2) (hk : 0 < kappa) :
    LocallyIntegrable (retainedCollisionMajorant (m := m) kappa p) volume := by
  have hF := (retainedSineBlock_continuous m).locallyIntegrable.add
    ((retainedBlockPole_locallyIntegrable hm hbudget).smul (1 / kappa ^ p))
  have hmeas : Measurable (retainedCollisionMajorant (m := m) kappa p) := by
    exact (retainedSineBlock_continuous m).measurable.div
      ((measurable_const.min (measurable_const.mul (angularQuadratic_continuous m).measurable)).pow_const p)
  apply hF.mono hmeas.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro x
  have hv := retainedSineBlock_nonneg x
  have hp : 0 ≤ (1 / kappa ^ p) * retainedBlockPole p x := by
    exact mul_nonneg (by positivity) (div_nonneg hv (pow_nonneg (angularQuadratic_nonneg x) p))
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Real.norm_of_nonneg (retainedCollisionMajorant_nonneg hk.le x), Real.norm_of_nonneg (add_nonneg hv hp)]
  exact retainedCollisionMajorant_le hk x

theorem retainedCollisionMajorant_integrable {m p : ℕ} {kappa : ℝ}
    (hm : 0 < m) (hbudget : 2 * p < m ^ 2) (hk : 0 < kappa) :
    IntegrableOn (retainedCollisionMajorant (m := m) kappa p) (regularAngularBox m) :=
  (retainedCollisionMajorant_locallyIntegrable hm hbudget hk).integrableOn_isCompact
    (regularAngularBox_compact m)

end
end IsingBulk.AnisoF002.RegularTail.C03
