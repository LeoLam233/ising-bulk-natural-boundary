import IsingBulk.Preferred22.BumpCoarea

/-! The source one-body integrations on every mean/diameter scale. -/
namespace IsingBulk.Preferred22
noncomputable section
open scoped BigOperators Topology
open Set MeasureTheory

def preferredOneBodyMajorant (ε u : ℝ) : ℝ := 1/Real.sqrt (|u|+ε)

theorem preferredOneBodyMajorant_continuous {ε : ℝ} (hε : 0 < ε) :
    Continuous (preferredOneBodyMajorant ε) := by
  exact continuous_const.div (Real.continuous_sqrt.comp (continuous_abs.add_const ε))
    (fun u => (Real.sqrt_pos.mpr (by positivity : 0 < |u|+ε)).ne')

theorem preferredOneBodyMajorant_nonneg {ε u : ℝ} : 0 ≤ preferredOneBodyMajorant ε u := by
  unfold preferredOneBodyMajorant
  positivity

theorem preferred_oneBody_positive_integral {ε R : ℝ} (hε : 0 < ε) (hR : 0 ≤ R) :
    (∫ u : ℝ in 0..R, preferredOneBodyMajorant ε u) =
      2*(Real.sqrt (R+ε)-Real.sqrt ε) := by
  have hd (u : ℝ) (hu : u ∈ uIcc 0 R) :
      HasDerivAt (fun x : ℝ => 2*Real.sqrt (x+ε)) (preferredOneBodyMajorant ε u) u := by
    rw [uIcc_of_le hR] at hu
    have hpos : 0 < u+ε := by linarith [hu.1]
    have h := (((Real.hasDerivAt_sqrt hpos.ne').comp u ((hasDerivAt_id u).add_const ε)).const_mul 2)
    convert! h using 1
    dsimp [preferredOneBodyMajorant]
    rw [abs_of_nonneg hu.1]
    ring
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((preferredOneBodyMajorant_continuous hε).intervalIntegrable 0 R)
  calc
    _ = 2*Real.sqrt (R+ε)-2*Real.sqrt (0+ε) := he
    _ = _ := by rw [zero_add]; ring

theorem preferred_oneBody_symmetric_integral {ε R : ℝ} (hε : 0 < ε) (hR : 0 ≤ R) :
    (∫ u : ℝ in (-R)..R, preferredOneBodyMajorant ε u) =
      4*(Real.sqrt (R+ε)-Real.sqrt ε) := by
  have hc := preferredOneBodyMajorant_continuous hε
  have hneg : (∫ u : ℝ in (-R)..0, preferredOneBodyMajorant ε u) =
      ∫ u : ℝ in 0..R, preferredOneBodyMajorant ε u := by
    simpa only [preferredOneBodyMajorant,abs_neg,neg_zero] using
      (intervalIntegral.integral_comp_neg (preferredOneBodyMajorant ε) (a := 0) (b := R)).symm
  rw [← intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable (-R) 0)
    (hc.intervalIntegrable 0 R),hneg,preferred_oneBody_positive_integral hε hR]
  ring

set_option maxHeartbeats 600000 in
/-- The exact source q22 estimate holds for every r>0 and epsilon>0,
including intervals crossing the branch and arbitrarily small diameters. -/
theorem preferred_oneBody_mean_scale {ε r : ℝ} (hε : 0 < ε) (hr : 0 < r) (t : ℝ) :
    (∫ u : ℝ in (t-2*r)..(t+2*r), preferredOneBodyMajorant ε u) ≤
      32*r/Real.sqrt (|t|+r+ε) := by
  have hc := preferredOneBodyMajorant_continuous hε
  have hT : 0 < |t|+r+ε := by positivity
  have hTs : 0 < Real.sqrt (|t|+r+ε) := Real.sqrt_pos.mpr hT
  have hab : t-2*r ≤ t+2*r := by linarith
  by_cases hfar : 4*r ≤ |t|
  · have hp (u : ℝ) (hu : u ∈ Icc (t-2*r) (t+2*r)) :
        preferredOneBodyMajorant ε u ≤ 2/Real.sqrt (|t|+r+ε) := by
      have hut : |t-u| ≤ 2*r := abs_le.mpr ⟨by linarith [hu.2],by linarith [hu.1]⟩
      have htu : |t| ≤ |u|+2*r := by
        have h := abs_add_le (t-u) u
        rw [sub_add_cancel] at h
        linarith
      have hscale : |t|+r+ε ≤ 4*(|u|+ε) := by linarith [abs_nonneg u]
      have hs := Real.sqrt_le_sqrt hscale
      rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4)] at hs
      norm_num at hs
      have hus : 0 < Real.sqrt (|u|+ε) := Real.sqrt_pos.mpr (by positivity)
      exact (div_le_div_iff₀ hus hTs).mpr (by simpa only [one_mul] using hs)
    have hi := intervalIntegral.integral_mono_on (μ := volume) hab (hc.intervalIntegrable _ _)
      (continuous_const.intervalIntegrable _ _) hp
    calc
      _ ≤ ∫ _u : ℝ in (t-2*r)..(t+2*r), 2/Real.sqrt (|t|+r+ε) := hi
      _ = 8*r/Real.sqrt (|t|+r+ε) := by rw [intervalIntegral.integral_const]; simp only [smul_eq_mul]; ring
      _ ≤ _ := div_le_div_of_nonneg_right (by nlinarith) hTs.le
  · have ht := abs_le.mp (show |t| ≤ 4*r by linarith)
    have hleft : -6*r ≤ t-2*r := by linarith [ht.1]
    have hright : t+2*r ≤ 6*r := by linarith [ht.2]
    have hi := intervalIntegral.integral_mono_interval (μ := volume) hleft hab hright
      (Filter.Eventually.of_forall (fun u : ℝ => preferredOneBodyMajorant_nonneg (ε := ε) (u := u)))
      (hc.intervalIntegrable (-6*r) (6*r))
    have hR : 0 ≤ 6*r := by positivity
    have hRe : 0 < 6*r+ε := by positivity
    have hRsum : 0 < Real.sqrt (6*r+ε)+Real.sqrt ε := by positivity
    have hid : 4*(Real.sqrt (6*r+ε)-Real.sqrt ε) =
        24*r/(Real.sqrt (6*r+ε)+Real.sqrt ε) := by
      apply (eq_div_iff hRsum.ne').mpr
      nlinarith [Real.sq_sqrt hRe.le,Real.sq_sqrt hε.le]
    have hTle : |t|+r+ε ≤ 6*r+ε := by linarith
    calc
      _ ≤ ∫ u : ℝ in (-6*r)..(6*r), preferredOneBodyMajorant ε u := hi
      _ = 4*(Real.sqrt (6*r+ε)-Real.sqrt ε) :=
        by simpa only [neg_mul] using preferred_oneBody_symmetric_integral hε hR
      _ = 24*r/(Real.sqrt (6*r+ε)+Real.sqrt ε) := hid
      _ ≤ 24*r/Real.sqrt (6*r+ε) := div_le_div_of_nonneg_left (by positivity)
        (Real.sqrt_pos.mpr hRe) (le_add_of_nonneg_right (Real.sqrt_nonneg ε))
      _ ≤ 24*r/Real.sqrt (|t|+r+ε) := div_le_div_of_nonneg_left (by positivity) hTs
        (Real.sqrt_le_sqrt hTle)
      _ ≤ _ := div_le_div_of_nonneg_right (by nlinarith) hTs.le

def preferredReciprocalMajorant (ε u : ℝ) : ℝ := 1/(|u|+ε)

theorem preferredReciprocalMajorant_continuous {ε : ℝ} (hε : 0 < ε) :
    Continuous (preferredReciprocalMajorant ε) :=
  continuous_const.div (continuous_abs.add_const ε) (fun u => (by positivity : 0 < |u|+ε).ne')

theorem preferredReciprocalMajorant_nonneg {ε u : ℝ} (hε : 0 ≤ ε) :
    0 ≤ preferredReciprocalMajorant ε u := by unfold preferredReciprocalMajorant; positivity

theorem preferred_reciprocal_positive_integral {ε R : ℝ} (hε : 0 < ε) (hR : 0 ≤ R) :
    (∫ u : ℝ in 0..R, preferredReciprocalMajorant ε u) = Real.log (R+ε)-Real.log ε := by
  have hd (u : ℝ) (hu : u ∈ uIcc 0 R) :
      HasDerivAt (fun x : ℝ => Real.log (x+ε)) (preferredReciprocalMajorant ε u) u := by
    rw [uIcc_of_le hR] at hu
    have hp : 0 < u+ε := by linarith [hu.1]
    have h := (Real.hasDerivAt_log hp.ne').comp u ((hasDerivAt_id u).add_const ε)
    convert! h using 1
    simp only [preferredReciprocalMajorant,abs_of_nonneg hu.1,mul_one,one_div]
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((preferredReciprocalMajorant_continuous hε).intervalIntegrable 0 R)
  simpa only [zero_add] using he

theorem preferred_reciprocal_symmetric_integral {ε R : ℝ} (hε : 0 < ε) (hR : 0 ≤ R) :
    (∫ u : ℝ in (-R)..R, preferredReciprocalMajorant ε u) =
      2*(Real.log (R+ε)-Real.log ε) := by
  have hc := preferredReciprocalMajorant_continuous hε
  have hneg : (∫ u : ℝ in (-R)..0, preferredReciprocalMajorant ε u) =
      ∫ u : ℝ in 0..R, preferredReciprocalMajorant ε u := by
    simpa only [preferredReciprocalMajorant,abs_neg,neg_zero] using
      (intervalIntegral.integral_comp_neg (preferredReciprocalMajorant ε) (a := 0) (b := R)).symm
  rw [← intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable (-R) 0)
    (hc.intervalIntegrable 0 R),hneg,preferred_reciprocal_positive_integral hε hR]
  ring

theorem preferred_reciprocal_logarithmic_bound {ε R : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hR : 0 ≤ R) :
    (∫ u : ℝ in (-R)..R, preferredReciprocalMajorant ε u) ≤
      (2*(1+|Real.log (R+1)|))*(1+|Real.log ε|) := by
  rw [preferred_reciprocal_symmetric_integral hε hR]
  have hlog : Real.log (R+ε) ≤ Real.log (R+1) :=
    Real.log_le_log (by positivity) (by linarith)
  nlinarith [le_abs_self (Real.log (R+1)),neg_le_abs (Real.log ε),
    mul_nonneg (abs_nonneg (Real.log (R+1))) (abs_nonneg (Real.log ε))]

/-- The reciprocal integrates logarithmically on every bounded affine
extreme slice; no component-count hypothesis is used. -/
theorem preferred_reciprocal_affine_add {ε R a x y : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hR : 0 ≤ R) (hxy : x ≤ y)
    (hx : -R ≤ a+x) (hy : a+y ≤ R) :
    (∫ t : ℝ in x..y, preferredReciprocalMajorant ε (a+t)) ≤
      (2*(1+|Real.log (R+1)|))*(1+|Real.log ε|) := by
  rw [intervalIntegral.integral_comp_add_left]
  apply le_trans _ (preferred_reciprocal_logarithmic_bound hε hε1 hR)
  exact intervalIntegral.integral_mono_interval hx (by linarith) hy
    (Filter.Eventually.of_forall (fun u : ℝ => preferredReciprocalMajorant_nonneg (u := u) hε.le))
    ((preferredReciprocalMajorant_continuous hε).intervalIntegrable (-R) R)

theorem preferred_reciprocal_affine_sub {ε R a x y : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hR : 0 ≤ R) (hxy : x ≤ y)
    (hx : a-x ≤ R) (hy : -R ≤ a-y) :
    (∫ t : ℝ in x..y, preferredReciprocalMajorant ε (a-t)) ≤
      (2*(1+|Real.log (R+1)|))*(1+|Real.log ε|) := by
  rw [intervalIntegral.integral_comp_sub_left]
  apply le_trans _ (preferred_reciprocal_logarithmic_bound hε hε1 hR)
  exact intervalIntegral.integral_mono_interval hy (by linarith) hx
    (Filter.Eventually.of_forall (fun u : ℝ => preferredReciprocalMajorant_nonneg (u := u) hε.le))
    ((preferredReciprocalMajorant_continuous hε).intervalIntegrable (-R) R)

end
end IsingBulk.Preferred22
