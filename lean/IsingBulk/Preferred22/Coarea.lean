import IsingBulk.Tail.SimpleKernelBounds
import IsingBulk.Preferred22.Contour
import IsingBulk.Preferred22.Coordinates
import IsingBulk.Analysis.BranchSecondDerivative
import IsingBulk.Analysis.BranchUpper
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Preferred22: scalar coarea ingredients

This module proves source-specific ingredients of §8. It does not assume or
claim the occupancy-dependent coarea theorem. The imported source file
`Tail.SimpleKernelBounds` contains scalar exponential-kernel estimates only;
it imports Mathlib and no physical or full-tail theorem.
-/
namespace IsingBulk.Preferred22
noncomputable section
open scoped BigOperators
open Set MeasureTheory Filter
open scoped Topology

/-- The exact complex Jacobian column of the balanced displacement, with
`κ = I * τ / N`. This notation retains both occupancy derivatives. -/
def occupancyJacobianColumn {ι : Type*} [Fintype ι] [DecidableEq ι]
    (κ : ℂ) (p m dp dm : ι → ℂ) (i v : ι) : ℂ :=
  (if v = i then 1 - κ * ((∑ j, p j) * dm i - (∑ j, m j) * dp i) else 0)
    - κ * m v * dp i + κ * p v * dm i

/-- Equation (8.5): summing the exact full Jacobian column against the
one-body phase slopes produces both global occupancy corrections. -/
theorem occupancy_phase_column {ι : Type*} [Fintype ι] [DecidableEq ι]
    (κ : ℂ) (p m dp dm b : ι → ℂ) (i : ι) :
    (∑ v, b v * occupancyJacobianColumn κ p m dp dm i v) =
      b i * (1 - κ * ((∑ j, p j) * dm i - (∑ j, m j) * dp i))
        - κ * dp i * (∑ v, m v * b v)
        + κ * dm i * (∑ v, p v * b v) := by
  simp only [occupancyJacobianColumn, mul_add, mul_sub,
    Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have hm : (∑ v, b v * (κ * m v * dp i)) = κ * dp i * (∑ v, m v * b v) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    ring
  have hp : (∑ v, b v * (κ * p v * dm i)) = κ * dm i * (∑ v, p v * b v) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    ring
  rw [hm, hp]
  ring

/-- The constrained extreme direction differentiates the minimum and maximum
with opposite signs, so the two occupancy coefficients occur as differences. -/
theorem occupancy_extreme_difference {ι : Type*} [Fintype ι] [DecidableEq ι]
    (κ : ℂ) (p m dp dm b : ι → ℂ) (i j : ι) :
    (∑ v, b v * occupancyJacobianColumn κ p m dp dm i v) -
      (∑ v, b v * occupancyJacobianColumn κ p m dp dm j v) =
    (b i * (1 - κ * ((∑ v, p v) * dm i - (∑ v, m v) * dp i)) -
     b j * (1 - κ * ((∑ v, p v) * dm j - (∑ v, m v) * dp j))) -
      κ * (dp i - dp j) * (∑ v, m v * b v) +
      κ * (dm i - dm j) * (∑ v, p v * b v) := by
  rw [occupancy_phase_column, occupancy_phase_column]
  ring

/-- Absorption of the true occupancy correction into the positive oblique
projection. Unlike a Hessian argument along a transposition path, only the
actual base derivative and correction at this configuration are used. -/
theorem oblique_correction_absorption {ω base err : ℂ} {c L : ℝ}
    (hc : 0 < c) (hL : 0 < L) (hω : ‖ω‖ ≤ 1)
    (hbase : c * L ≤ (ω * base).re) (herr : ‖err‖ ≤ c * L / 2) :
    c * L / 2 ≤ (ω * (base + err)).re ∧ 0 < (ω * (base + err)).re := by
  have hnorm : ‖ω * err‖ ≤ c * L / 2 := by
    calc
      ‖ω * err‖ = ‖ω‖ * ‖err‖ := norm_mul _ _
      _ ≤ 1 * ‖err‖ := mul_le_mul_of_nonneg_right hω (norm_nonneg _)
      _ ≤ c * L / 2 := by simpa using herr
  have hre : -(c * L / 2) ≤ (ω * err).re := by
    have h := Complex.abs_re_le_norm (ω * err)
    exact (neg_le_abs _).trans (h.trans hnorm) |> fun h => by linarith
  have hsum : c * L / 2 ≤ (ω * (base + err)).re := by
    rw [mul_add, Complex.add_re]
    linarith
  exact ⟨hsum, (by positivity : 0 < c * L / 2).trans_le hsum⟩

/-- Equation (8.8), the negative-minimum bound. No positive lower diameter
cutoff relative to epsilon is required. -/
theorem negative_minimum_pair_bound {a b r : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) (hab : r ≤ a + b) :
    1 / (a * Real.sqrt b) ≤
      1 / Real.sqrt r * (1 / a + 1 / b) := by
  have hsa : 0 < Real.sqrt r := Real.sqrt_pos.2 hr
  have hsb : 0 < Real.sqrt b := Real.sqrt_pos.2 hb
  have hs : Real.sqrt r * Real.sqrt b ≤ a + b := by
    have h1 := Real.sq_sqrt hr.le
    have h2 := Real.sq_sqrt hb.le
    have h3 : r * b ≤ (a + b)^2 := by nlinarith
    have hp : 0 ≤ Real.sqrt r * Real.sqrt b := by positivity
    nlinarith [sq_nonneg (a + b - Real.sqrt r * Real.sqrt b)]
  apply (div_le_iff₀ (mul_pos ha hsb)).2
  have he : (1 / Real.sqrt r * (1 / a + 1 / b)) * (a * Real.sqrt b) =
      (a + b) / (Real.sqrt r * Real.sqrt b) := by
    field_simp
    nlinarith [Real.sq_sqrt hb.le]
  rw [he]
  exact (le_div_iff₀ (mul_pos hsa hsb)).2 (by simpa using hs)

/-- Exact rational form of the square-root integral in (8.4). -/
theorem inverse_sqrt_difference {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    2 / Real.sqrt x - 2 / Real.sqrt y =
      2 * (y - x) /
        (Real.sqrt x * Real.sqrt y * (Real.sqrt x + Real.sqrt y)) := by
  have hsx := Real.sqrt_pos.2 hx
  have hsy := Real.sqrt_pos.2 hy
  field_simp
  nlinarith [Real.sq_sqrt hx.le, Real.sq_sqrt hy.le]


/-- The actual real lattice in the projected phase variable. -/
def projectedLattice (c : ℝ) : Set ℝ :=
  Set.range (fun n : ℤ => (n : ℝ) * (2 * Real.pi * c))

/-- Distance to the projected period lattice, rather than the unprojected
phase distance. -/
def projectedDistance (c v : ℝ) : ℝ := Metric.infDist v (projectedLattice c)

theorem projectedDistance_nonneg (c v : ℝ) : 0 ≤ projectedDistance c v :=
  Metric.infDist_nonneg

theorem projectedDistance_le_index (c v : ℝ) (n : ℤ) :
    projectedDistance c v ≤ |v - (n : ℝ) * (2 * Real.pi * c)| := by
  exact (Metric.infDist_le_dist_of_mem (show (n : ℝ) * (2 * Real.pi * c) ∈
    projectedLattice c from ⟨n, rfl⟩)).trans_eq (Real.dist_eq _ _)

/-- A nearest lattice cell is explicitly constructed by the floor function. -/
theorem exists_period_representative {P : ℝ} (hP : 0 < P) (v : ℝ) :
    ∃ n : ℤ, |v - (n : ℝ) * P| ≤ P / 2 := by
  let n : ℤ := ⌊v / P + 1/2⌋
  have h1 : (n : ℝ) ≤ v / P + 1/2 := Int.floor_le _
  have h2 : v / P + 1/2 < (n : ℝ) + 1 := Int.lt_floor_add_one _
  have h1' := mul_le_mul_of_nonneg_right h1 hP.le
  have h2' := mul_lt_mul_of_pos_right h2 hP
  have hcancel : v / P * P = v := div_mul_cancel₀ _ hP.ne'
  refine ⟨n, abs_le.mpr ⟨?_, ?_⟩⟩ <;> nlinarith

theorem projectedDistance_le_half_period {c : ℝ} (hc : 0 < c) (v : ℝ) :
    projectedDistance c v ≤ Real.pi * c := by
  obtain ⟨n, hn⟩ := exists_period_representative (by positivity : 0 < 2*Real.pi*c) v
  exact (projectedDistance_le_index c v n).trans (by nlinarith)

/-- The constant for the oblique kernel includes both small and large
attenuation. It is independent of a, a0, x and particle number. -/
def obliqueKernelConstant (c s : ℝ) : ℝ :=
  max ((1 + |s|) * Real.exp 1 + c * Real.pi)
    ((1 + Real.pi * c) / (1 - Real.exp (-1)))

/-- New oblique-kernel theorem of Preferred22 Lemma 8.1, for the general
projection v = c x - s a with c > 0. Taking c = cos(theta), s = sin(theta)
gives the manuscript's oblique projection. -/
theorem oblique_periodic_kernel {c s a0 a x : ℝ}
    (hc : 0 < c) (ha0 : 0 < a0) (ha01 : a0 ≤ 1) (ha : a0 ≤ a) :
    (IsingBulk.Tail.phaseDenominator (Real.exp (-a)) x)⁻¹ ≤
      obliqueKernelConstant c s /
        (a0 + projectedDistance c (c*x-s*a)) := by
  let D := IsingBulk.Tail.phaseDenominator (Real.exp (-a)) x
  let δ := projectedDistance c (c*x-s*a)
  have hap : 0 < a := ha0.trans_le ha
  have hd : 0 < D := by
    have h := IsingBulk.Tail.radial_deficit_le_phaseDenominator
      (Real.exp_pos (-a)).le x
    have he : Real.exp (-a) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    dsimp [D]
    linarith
  have hδ : 0 ≤ δ := projectedDistance_nonneg _ _
  have hb : 0 < a0 + δ := by linarith
  have hmain : a0 + δ ≤ obliqueKernelConstant c s * D := by
    by_cases ha1 : a ≤ 1
    · obtain ⟨n, hn⟩ := exists_period_representative
        (by positivity : 0 < 2*Real.pi) x
      have hn' : |x - (n : ℝ) * (2*Real.pi)| ≤ Real.pi := by nlinarith
      have hperiod : IsingBulk.Tail.phaseDenominator (Real.exp (-a))
          (x-(n : ℝ)*(2*Real.pi)) = D := by
        simpa only [zsmul_eq_mul] using
          (IsingBulk.Tail.phaseDenominator_periodic (Real.exp (-a))).sub_zsmul_eq (x := x) n
      have hx := IsingBulk.Tail.phase_distance_le_denominator
        (Real.exp_pos (-a)).le
        (Real.exp_le_one_iff.mpr (by linarith : -a ≤ 0)) hn'
      rw [hperiod] at hx
      have hat := IsingBulk.Tail.attenuation_le_denominator hap.le ha1 (t := x)
      change a ≤ Real.exp 1 * D at hat
      have hdelt : δ ≤ c * |x-(n : ℝ)*(2*Real.pi)| + |s| * a := by
        calc
          δ ≤ |(c*x-s*a) - (n : ℝ)*(2*Real.pi*c)| :=
            projectedDistance_le_index _ _ n
          _ = |c*(x-(n : ℝ)*(2*Real.pi))-s*a| := by congr 1; ring
          _ ≤ |c*(x-(n : ℝ)*(2*Real.pi))| + |s*a| := abs_sub _ _
          _ = c * |x-(n : ℝ)*(2*Real.pi)| + |s| * a := by
            rw [abs_mul, abs_mul, abs_of_pos hc, abs_of_pos hap]
      have hm1 := mul_le_mul_of_nonneg_left hat (show 0 ≤ 1+|s| by positivity)
      have hm2 := mul_le_mul_of_nonneg_left hx hc.le
      have hs : a0+δ ≤ ((1+|s|)*Real.exp 1+c*Real.pi)*D := by nlinarith
      exact hs.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hd.le)
    · have hge : 1 ≤ a := by linarith
      have hgappos : 0 < 1 - Real.exp (-1) := by
        have he : Real.exp (-1) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
        linarith
      have hgap : 1-Real.exp (-1) ≤ D := by
        have hh := IsingBulk.Tail.radial_deficit_le_phaseDenominator
          (Real.exp_pos (-a)).le x
        have he : Real.exp (-a) ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by linarith)
        dsimp [D]
        linarith
      have hbound : a0 + δ ≤ 1 + Real.pi*c := by
        have hh := projectedDistance_le_half_period hc (c*x-s*a)
        change δ ≤ Real.pi*c at hh
        linarith
      have hm := mul_le_mul_of_nonneg_left hgap
        (show 0 ≤ (1+Real.pi*c)/(1-Real.exp (-1)) by positivity)
      have he : (1+Real.pi*c)/(1-Real.exp (-1))*(1-Real.exp (-1)) =
          1+Real.pi*c := div_mul_cancel₀ _ hgappos.ne'
      rw [he] at hm
      exact (hbound.trans hm).trans
        (mul_le_mul_of_nonneg_right (le_max_right _ _) hd.le)
  change D⁻¹ ≤ obliqueKernelConstant c s / (a0+δ)
  rw [← one_div]
  exact (div_le_div_iff₀ hd hb).mpr (by simpa using hmain)


/-- Upper chord estimate, used to integrate the distance majorant through the
already proved scalar periodic exponential kernel. -/
theorem phase_denominator_le_attenuation_add_abs {a : ℝ} (ha : 0 ≤ a) (t : ℝ) :
    IsingBulk.Tail.phaseDenominator (Real.exp (-a)) t ≤ a + |t| := by
  let E := Complex.exp (Complex.I * (t : ℂ))
  let r := Real.exp (-a)
  have he : ‖E‖ = 1 := by simp [E]
  have hr : r ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hgap : 1-r ≤ a := by
    have h := Real.add_one_le_exp (-a)
    dsimp [r]
    linarith
  have hchord : ‖1-E‖ ≤ |t| := by
    rw [norm_sub_rev]
    dsimp [E]
    rw [Complex.norm_exp_I_mul_ofReal_sub_one]
    have h := Real.abs_sin_le_abs (x := t/2)
    rw [abs_div] at h
    norm_num at h
    norm_num [Real.norm_eq_abs, abs_mul]
    linarith
  have htri : ‖1-(r : ℂ)*E‖ ≤ ‖1-E‖ + ‖(1-(r : ℂ))*E‖ := by
    convert norm_add_le (1-E) ((1-(r : ℂ))*E) using 1
    congr 1
    ring
  have hnorm : ‖(1-(r : ℂ))*E‖ = 1-r := by
    rw [norm_mul, he, mul_one]
    norm_cast
    exact abs_of_nonneg (by linarith)
  rw [hnorm] at htri
  exact htri.trans (by linarith)

/-- The upper chord estimate descends to the actual infimum distance over
all projected lattice translates. -/
theorem phase_denominator_le_projectedDistance {c a : ℝ}
    (hc : 0 < c) (ha : 0 ≤ a) (v : ℝ) :
    IsingBulk.Tail.phaseDenominator (Real.exp (-a)) (v/c) ≤
      a + projectedDistance c v / c := by
  let D := IsingBulk.Tail.phaseDenominator (Real.exp (-a)) (v/c)
  have hlow : c*D-c*a ≤ projectedDistance c v := by
    apply (Metric.le_infDist (show (projectedLattice c).Nonempty from ⟨0, ⟨0, by simp⟩⟩)).2
    intro y hy
    obtain ⟨n, rfl⟩ := hy
    have hperiod : IsingBulk.Tail.phaseDenominator (Real.exp (-a))
        (v/c-(n : ℝ)*(2*Real.pi)) = D := by
      simpa only [zsmul_eq_mul] using
        (IsingBulk.Tail.phaseDenominator_periodic (Real.exp (-a))).sub_zsmul_eq (x := v/c) n
    have hh := phase_denominator_le_attenuation_add_abs ha
      (v/c-(n : ℝ)*(2*Real.pi))
    rw [hperiod] at hh
    have hm := mul_le_mul_of_nonneg_left hh hc.le
    have he : c * |v/c-(n : ℝ)*(2*Real.pi)| =
        |v-(n : ℝ)*(2*Real.pi*c)| := by
      calc
        c * |v/c-(n : ℝ)*(2*Real.pi)| = |c*(v/c-(n : ℝ)*(2*Real.pi))| := by
          rw [abs_mul, abs_of_pos hc]
        _ = |v-(n : ℝ)*(2*Real.pi*c)| := by
          congr 1
          field_simp
    rw [mul_add, he] at hm
    rw [Real.dist_eq]
    linarith
  change D ≤ a + projectedDistance c v / c
  rw [show a + projectedDistance c v / c = (a*c+projectedDistance c v)/c by
    field_simp]
  apply (le_div_iff₀ hc).2
  nlinarith

/-- A scalar domination for the projected distance kernel, with fixed
attenuation a. This permits a direct logarithmic L1 estimate. -/
theorem projected_reciprocal_le_kernel {c a : ℝ} (hc : 0 < c) (ha : 0 < a) (v : ℝ) :
    (a + projectedDistance c v)⁻¹ ≤
      max 1 c⁻¹ * (IsingBulk.Tail.phaseDenominator (Real.exp (-a)) (v/c))⁻¹ := by
  let D := IsingBulk.Tail.phaseDenominator (Real.exp (-a)) (v/c)
  let δ := projectedDistance c v
  have hδ : 0 ≤ δ := projectedDistance_nonneg _ _
  have hd : 0 < D := by
    have h := IsingBulk.Tail.radial_deficit_le_phaseDenominator
      (Real.exp_pos (-a)).le (v/c)
    have he : Real.exp (-a) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    dsimp [D]
    linarith
  have hbound := phase_denominator_le_projectedDistance hc ha.le v
  change D ≤ a + δ/c at hbound
  have hm1 := mul_le_mul_of_nonneg_right (le_max_left 1 c⁻¹) ha.le
  have hm2 := mul_le_mul_of_nonneg_right (le_max_right 1 c⁻¹) hδ
  have hb : D ≤ max 1 c⁻¹ * (a+δ) := by
    rw [div_eq_mul_inv] at hbound
    nlinarith
  change (a+δ)⁻¹ ≤ max 1 c⁻¹ * D⁻¹
  rw [← one_div, ← div_eq_mul_inv]
  apply (div_le_div_iff₀ (by positivity : 0 < a+δ) hd).2
  simpa using hb

/-- The projected reciprocal majorant is a continuous genuine function of
v; its integration does not require a number-of-cutoff-components premise. -/
theorem projected_reciprocal_continuous {c a : ℝ} (ha : 0 < a) :
    Continuous (fun v : ℝ => (a + projectedDistance c v)⁻¹) := by
  apply Continuous.inv₀
  · exact continuous_const.add (Metric.continuous_infDist_pt (projectedLattice c))
  · intro v
    exact ne_of_gt (add_pos_of_pos_of_nonneg ha (projectedDistance_nonneg _ _))


/-- The logarithmic integral bound for the projected distance majorant on
an arbitrary interval, counted in complete projected periods. -/
theorem projected_kernel_interval_integral {c a x y : ℝ}
    (hc : 0 < c) (ha : 0 < a) (ha1 : a ≤ 1)
    (n : ℕ) (hxy : x ≤ y) (hlen : y ≤ x + (n : ℝ)*(2*Real.pi*c)) :
    (∫ v : ℝ in x..y, (a + projectedDistance c v)⁻¹) ≤
      (c * max 1 c⁻¹) *
        ((n : ℝ) * IsingBulk.Tail.simpleKernelConstant * (1+|Real.log a|)) := by
  let f := fun t : ℝ => (IsingBulk.Tail.phaseDenominator (Real.exp (-a)) t)⁻¹
  let K := max 1 c⁻¹
  have hfc : Continuous f := IsingBulk.Tail.simple_kernel_continuous ha
  have hgc : Continuous (fun v : ℝ => K * f (v/c)) :=
    continuous_const.mul (hfc.comp (continuous_id.div_const c))
  have hdom : (∫ v : ℝ in x..y, (a + projectedDistance c v)⁻¹) ≤
      ∫ v : ℝ in x..y, K * f (v/c) := by
    apply intervalIntegral.integral_mono_on hxy
      ((projected_reciprocal_continuous ha).intervalIntegrable _ _)
      (hgc.intervalIntegrable _ _)
    intro v _
    exact projected_reciprocal_le_kernel hc ha v
  have hxy' : x/c ≤ y/c := div_le_div_of_nonneg_right hxy hc.le
  have hlen' : y/c ≤ x/c + (n : ℝ)*(2*Real.pi) := by
    apply (div_le_iff₀ hc).2
    calc
      y ≤ x + (n : ℝ)*(2*Real.pi*c) := hlen
      _ = (x/c + (n : ℝ)*(2*Real.pi))*c := by field_simp
  have hk := IsingBulk.Tail.simple_kernel_interval_integral ha ha1 n hxy' hlen'
  change (∫ t : ℝ in x/c..y/c, f t) ≤ _ at hk
  calc
    (∫ v : ℝ in x..y, (a + projectedDistance c v)⁻¹)
        ≤ ∫ v : ℝ in x..y, K * f (v/c) := hdom
    _ = (c*K) * (∫ t : ℝ in x/c..y/c, f t) := by
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_div f hc.ne']
      simp only [smul_eq_mul]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hk (by dsimp [K]; positivity)

/-- The period count can be eliminated, giving the exact O((1+L)(1+|log a|))
form of Preferred22 Lemma 8.1. -/
theorem projected_kernel_logarithmic_integral {c a x y : ℝ}
    (hc : 0 < c) (ha : 0 < a) (ha1 : a ≤ 1) (hxy : x ≤ y) :
    (∫ v : ℝ in x..y, (a + projectedDistance c v)⁻¹) ≤
      ((c + 1/(2*Real.pi)) * max 1 c⁻¹ * IsingBulk.Tail.simpleKernelConstant) *
        (1 + (y-x)) * (1+|Real.log a|) := by
  let P := 2*Real.pi*c
  let L := y-x
  have hP : 0 < P := by dsimp [P]; positivity
  have hL : 0 ≤ L := sub_nonneg.mpr hxy
  let n := ⌊L/P⌋₊+1
  have hnupper : (n : ℝ) ≤ L/P+1 := by
    have h := Nat.floor_le (div_nonneg hL hP.le)
    dsimp [n]
    push_cast
    linarith
  have hnlower : L/P < (n : ℝ) := by
    simpa only [n, Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one (L/P)
  have hlen : y ≤ x + (n : ℝ)*(2*Real.pi*c) := by
    have h := (div_lt_iff₀ hP).mp hnlower
    dsimp [P, L] at h
    linarith
  have hk := projected_kernel_interval_integral hc ha ha1 n hxy hlen
  have hn : c * (n : ℝ) ≤ (c+1/(2*Real.pi))*(1+L) := by
    have h := mul_le_mul_of_nonneg_left hnupper hc.le
    have he : c*(L/P+1) = c + L/(2*Real.pi) := by
      dsimp [P]
      field_simp
      ring
    rw [he] at h
    have hcp : 0 ≤ c*L := mul_nonneg hc.le hL
    have hpinv : 0 ≤ 1/(2*Real.pi) := by positivity
    simp only [div_eq_mul_inv] at h hpinv ⊢
    nlinarith
  have hm := mul_le_mul_of_nonneg_right hn
    (show 0 ≤ max 1 c⁻¹ * IsingBulk.Tail.simpleKernelConstant *
      (1+|Real.log a|) by positivity [IsingBulk.Tail.simpleKernelConstant_pos])
  exact hk.trans (by dsimp [L] at hm; nlinarith [hm])


/-- The actual balanced contour point with κ = τ/N, evaluated using smooth
real occupancies. The real bump functions are not holomorphically extended. -/
def balancedContourPoint {ι : Type*} [Fintype ι] (κ : ℝ)
    (p m : ℝ → ℝ) (θ : ι → ℝ) (v : ι) : ℂ :=
  (θ v : ℂ) - Complex.I * (κ : ℂ) *
    (((∑ j, p (θ j)) * m (θ v) - (∑ j, m (θ j)) * p (θ v) : ℝ) : ℂ)

/-- The velocity of the balanced contour along an actual real angular path.
It includes derivatives of both global occupancies and both local factors. -/
def balancedContourVelocity {ι : Type*} [Fintype ι] (κ : ℝ)
    (p m : ℝ → ℝ) (θ θdot dp dm : ι → ℝ) (v : ι) : ℂ :=
  (θdot v : ℂ) - Complex.I * (κ : ℂ) *
    (((∑ j, dp j * θdot j) * m (θ v) +
       (∑ j, p (θ j)) * (dm v * θdot v) -
       ((∑ j, dm j * θdot j) * p (θ v) +
       (∑ j, m (θ j)) * (dp v * θdot v)) : ℝ) : ℂ)

/-- Full real chain rule for the balanced contour, with arbitrary smooth
occupancies p,m and arbitrary real angular motion. -/
theorem hasDerivAt_balancedContourPoint {ι : Type*} [Fintype ι]
    {κ t0 : ℝ} {p m : ℝ → ℝ} {θ : ℝ → ι → ℝ} {θdot dp dm : ι → ℝ}
    (hθ : ∀ v, HasDerivAt (fun t => θ t v) (θdot v) t0)
    (hp : ∀ v, HasDerivAt p (dp v) (θ t0 v))
    (hm : ∀ v, HasDerivAt m (dm v) (θ t0 v)) (v : ι) :
    HasDerivAt (fun t => balancedContourPoint κ p m (θ t) v)
      (balancedContourVelocity κ p m (θ t0) θdot dp dm v) t0 := by
  have hpf (j : ι) := (hp j).comp t0 (hθ j)
  have hmf (j : ι) := (hm j).comp t0 (hθ j)
  have hP := HasDerivAt.sum (u := Finset.univ) (fun j _ => hpf j)
  have hQ := HasDerivAt.sum (u := Finset.univ) (fun j _ => hmf j)
  have hh := (hP.mul (hmf v)).sub (hQ.mul (hpf v))
  have hw := (hθ v).ofReal_comp.sub (hh.ofReal_comp.const_mul (Complex.I * (κ : ℂ)))
  simpa [balancedContourPoint, balancedContourVelocity, Function.comp_def,
    Pi.sub_def, Finset.sum_fn] using hw

/-- Full real-to-complex chain rule for the total phase along the actual
balanced contour. The only phase premise is its pointwise complex derivative,
not a presumed derivative of the total phase. -/
theorem hasDerivAt_balancedPhase {ι : Type*} [Fintype ι]
    {κ t0 : ℝ} {p m : ℝ → ℝ} {θ : ℝ → ι → ℝ} {θdot dp dm : ι → ℝ}
    {φ : ℂ → ℂ} {b : ι → ℂ}
    (hθ : ∀ v, HasDerivAt (fun t => θ t v) (θdot v) t0)
    (hp : ∀ v, HasDerivAt p (dp v) (θ t0 v))
    (hm : ∀ v, HasDerivAt m (dm v) (θ t0 v))
    (hφ : ∀ v, HasDerivAt φ (b v) (balancedContourPoint κ p m (θ t0) v)) :
    HasDerivAt (fun t => ∑ v, φ (balancedContourPoint κ p m (θ t) v))
      (∑ v, b v * balancedContourVelocity κ p m (θ t0) θdot dp dm v) t0 := by
  have hv (v : ι) : HasDerivAt (fun t => φ (balancedContourPoint κ p m (θ t) v))
      (b v * balancedContourVelocity κ p m (θ t0) θdot dp dm v) t0 := by
    have hw := hasDerivAt_balancedContourPoint (κ := κ) hθ hp hm v
    simpa only [Function.comp_def, smul_eq_mul, mul_comm] using (hφ v).scomp t0 hw
  simpa only [Finset.sum_fn] using HasDerivAt.sum (u := Finset.univ) (fun v _ => hv v)

/-- For a coordinate motion the actual derivative equals the full Jacobian
column, with the occupancy derivatives still retained. -/
theorem balancedContourVelocity_column {ι : Type*} [Fintype ι] [DecidableEq ι]
    (κ : ℝ) (p m : ℝ → ℝ) (θ dp dm : ι → ℝ) (i v : ι) :
    balancedContourVelocity κ p m θ (fun j => if j=i then 1 else 0) dp dm v =
      occupancyJacobianColumn (Complex.I*(κ : ℂ))
        (fun j => (p (θ j) : ℂ)) (fun j => (m (θ j) : ℂ))
        (fun j => (dp j : ℂ)) (fun j => (dm j : ℂ)) i v := by
  simp only [balancedContourVelocity, occupancyJacobianColumn, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  by_cases hvi : v=i
  · subst v
    simp only [ite_true]
    push_cast
    ring
  · simp only [hvi, ite_false, add_zero]
    push_cast
    ring

/-- Equation (8.5) as an actual HasDerivAt theorem for the original smooth
real occupancy-dependent contour. This is the derivative used before the
minimum-minus-maximum comparison in the genuine coarea argument. -/
theorem hasDerivAt_totalPhase_coordinate {ι : Type*} [Fintype ι] [DecidableEq ι]
    {κ t0 : ℝ} {p m : ℝ → ℝ} {θ : ℝ → ι → ℝ} {dp dm : ι → ℝ}
    {φ : ℂ → ℂ} {b : ι → ℂ} (i : ι)
    (hθ : ∀ v, HasDerivAt (fun t => θ t v) (if v=i then 1 else 0) t0)
    (hp : ∀ v, HasDerivAt p (dp v) (θ t0 v))
    (hm : ∀ v, HasDerivAt m (dm v) (θ t0 v))
    (hφ : ∀ v, HasDerivAt φ (b v) (balancedContourPoint κ p m (θ t0) v)) :
    HasDerivAt (fun t => ∑ v, φ (balancedContourPoint κ p m (θ t) v))
      (b i * (1 - (Complex.I*(κ : ℂ)) *
        ((∑ j, (p (θ t0 j) : ℂ)) * (dm i : ℂ) -
         (∑ j, (m (θ t0 j) : ℂ)) * (dp i : ℂ))) -
       (Complex.I*(κ : ℂ)) * (dp i : ℂ) * (∑ v, (m (θ t0 v) : ℂ) * b v) +
       (Complex.I*(κ : ℂ)) * (dm i : ℂ) * (∑ v, (p (θ t0 v) : ℂ) * b v)) t0 := by
  have h := hasDerivAt_balancedPhase hθ hp hm hφ
  simp_rw [balancedContourVelocity_column] at h
  rw [occupancy_phase_column] at h
  exact h


/-- Agreement with the authoritative Preferred22 whole-contour definition. -/
theorem balancedContourPoint_eq_deformedAngles {N : ℕ} (τ : ℝ)
    (p m : ℝ → ℝ) (θ : Fin N → ℝ) (i : Fin N) :
    balancedContourPoint (τ/N) p m θ i = deformedAngles τ p m θ i := by
  unfold balancedContourPoint deformedAngles balancedShift occupancy
  push_cast
  ring

/-- The real part of the actual oblique phase, with the manuscript's sign. -/
theorem projected_phase_realpart (θ x a : ℝ) :
    (Complex.exp (-Complex.I*(θ : ℂ)) * ((x : ℂ)-Complex.I*(a : ℂ))).re =
      Real.cos θ * x - Real.sin θ * a := by
  simp [Complex.mul_re, Complex.exp_re, Complex.exp_im]

/-- Exact identification of |1-exp(-iG)| with the scalar kernel used above
for G=x-i a, including the orientation of the phase. -/
theorem actual_phase_denominator (x a : ℝ) :
    ‖1-Complex.exp (-Complex.I*((x : ℂ)-Complex.I*(a : ℂ)))‖ =
      IsingBulk.Tail.phaseDenominator (Real.exp (-a)) x := by
  have he : -Complex.I*((x : ℂ)-Complex.I*(a : ℂ)) =
      ((-a : ℝ) : ℂ)+Complex.I*((-x : ℝ) : ℂ) := by
    calc
      _ = -Complex.I*(x : ℂ)+Complex.I^2*(a : ℂ) := by ring
      _ = _ := by rw [Complex.I_sq]; push_cast; ring
  calc
    _ = IsingBulk.Tail.phaseDenominator (Real.exp (-a)) (-x) := by
      unfold IsingBulk.Tail.phaseDenominator
      rw [he, Complex.exp_add, Complex.ofReal_exp]
    _ = _ := IsingBulk.Tail.phaseDenominator_neg _ _

/-- Literal complex-phase version of the manuscript's oblique periodic
kernel inequality. -/
theorem actual_oblique_periodic_kernel {θ x a a0 : ℝ}
    (hθ : |θ| < Real.pi/2) (ha0 : 0 < a0) (ha01 : a0 ≤ 1) (ha : a0 ≤ a) :
    ‖1-Complex.exp (-Complex.I*((x : ℂ)-Complex.I*(a : ℂ)))‖⁻¹ ≤
      obliqueKernelConstant (Real.cos θ) (Real.sin θ) /
        (a0 + projectedDistance (Real.cos θ)
          (Complex.exp (-Complex.I*(θ : ℂ)) * ((x : ℂ)-Complex.I*(a : ℂ))).re) := by
  rw [actual_phase_denominator, projected_phase_realpart]
  exact oblique_periodic_kernel (Real.cos_pos_of_mem_Ioo (abs_lt.mp hθ)) ha0 ha01 ha

/-- Exact integration of the comparison curvature in (8.4). -/
theorem inverse_three_halves_integral {m M E : ℝ} (hm : 0 < m+E) (hMm : m ≤ M) :
    (∫ u : ℝ in m..M, (u+E)^(-(3/2 : ℝ))) =
      2 * ((m+E)^(-(1/2 : ℝ)) - (M+E)^(-(1/2 : ℝ))) := by
  have hpos (u : ℝ) (hu : u ∈ uIcc m M) : 0 < u+E := by
    rw [uIcc_of_le hMm] at hu
    linarith [hu.1]
  have hi : IntervalIntegrable (fun u : ℝ => (u+E)^(-(3/2 : ℝ))) volume m M := by
    exact ((continuousOn_id.add continuousOn_const).rpow_const
      (fun u hu => Or.inl (hpos u hu).ne')).intervalIntegrable
  have hd (u : ℝ) (hu : u ∈ uIcc m M) :
      HasDerivAt (fun v : ℝ => -2*(v+E)^(-(1/2 : ℝ))) ((u+E)^(-(3/2 : ℝ))) u := by
    have h := (((hasDerivAt_id u).add_const E).rpow_const
      (p := -(1/2 : ℝ)) (Or.inl (hpos u hu).ne')).const_mul (-2)
    convert h using 1
    norm_num
    ring_nf
    simp only [id_eq, add_comm]
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi
  convert h using 1
  ring

/-- Exact extreme-coordinate Jacobian algebra after the proved positive
projection lower bound. This is the square-root-over-diameter ratio in (8.1). -/
theorem extreme_jacobian_ratio {x y c K A D : ℝ}
    (hx : 0 < x) (hxy : x < y) (hc : 0 < c) (hK : 0 ≤ K)
    (hA : A ≤ K/(Real.sqrt x*Real.sqrt y))
    (hD : c*(2*(y-x)/(Real.sqrt x*Real.sqrt y*(Real.sqrt x+Real.sqrt y))) ≤ D) :
    A/D ≤ (K/c)*Real.sqrt y/(y-x) := by
  have hy : 0 < y := hx.trans hxy
  have hd : 0 < y-x := sub_pos.mpr hxy
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
  have hsy : 0 < Real.sqrt y := Real.sqrt_pos.2 hy
  have hL : 0 < c*(2*(y-x)/(Real.sqrt x*Real.sqrt y*(Real.sqrt x+Real.sqrt y))) :=
    by positivity
  have hDp : 0 < D := hL.trans_le hD
  calc
    A/D ≤ (K/(Real.sqrt x*Real.sqrt y))/D :=
      div_le_div_of_nonneg_right hA hDp.le
    _ ≤ (K/(Real.sqrt x*Real.sqrt y))/
        (c*(2*(y-x)/(Real.sqrt x*Real.sqrt y*(Real.sqrt x+Real.sqrt y)))) :=
      div_le_div_of_nonneg_left (by positivity) hL hD
    _ = K*(Real.sqrt x+Real.sqrt y)/(2*c*(y-x)) := by field_simp
    _ ≤ K*(2*Real.sqrt y)/(2*c*(y-x)) :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (by linarith [Real.sqrt_le_sqrt hxy.le]) hK)
        (by positivity)
    _ = (K/c)*Real.sqrt y/(y-x) := by field_simp


/-- The slope obtained by differentiating the actual dispersion relation. -/
def complexPhaseSlope (φ : ℂ → ℂ) (w : ℂ) : ℂ :=
  -Complex.sin w / Complex.sin (φ w)

/-- Local analytic dispersion, without a branch choice assumption beyond
its actual sine being nonzero, determines the exact first phase derivative. -/
theorem phase_deriv_of_local_dispersion {S w : ℂ} {φ : ℂ → ℂ}
    (hφ : DifferentiableAt ℂ φ w)
    (hdisp : (fun z => Complex.cos (φ z)) =ᶠ[𝓝 w] (fun z => S-Complex.cos z))
    (hsin : Complex.sin (φ w) ≠ 0) : deriv φ w = complexPhaseSlope φ w := by
  have hc := (Complex.hasDerivAt_cos (φ w)).comp w hφ.hasDerivAt
  have hd := (Complex.hasDerivAt_cos w).const_sub S
  have he := (hc.congr_of_eventuallyEq hdisp.symm).unique hd
  simp only [neg_neg] at he
  unfold complexPhaseSlope
  apply (eq_div_iff hsin).2
  linear_combination -he

/-- The algebraic reduction of the twice-differentiated dispersion to the
specific numerator S(1-S cos w+cos²w) in (8.3). -/
theorem phase_curvature_quotient (S x t y z : ℂ) (hz : z ≠ 0)
    (hy : y = S-x) (ht : t^2+x^2=1) (hp : z^2+y^2=1) :
    ((-x)*z-(-t)*(y*(-t/z)))/z^2 = -S*(1-S*x+x^2)/z^3 := by
  rw [hy] at hp ⊢
  field_simp
  linear_combination -x*hp - (S-x)*ht

/-- Actual complex second derivative formula on any regular analytic
physical-dispersion patch. All domain and branch regularity assumptions are
explicit; no coarea bound or phase-sector estimate is included in them. -/
theorem phase_second_hasDerivAt {S w : ℂ} {φ : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hw : w ∈ U) (hφ : AnalyticOnNhd ℂ φ U)
    (hdisp : ∀ z ∈ U, Complex.cos (φ z) = S-Complex.cos z)
    (hsin : ∀ z ∈ U, Complex.sin (φ z) ≠ 0) :
    HasDerivAt (deriv φ)
      (-S*(1-S*Complex.cos w+(Complex.cos w)^2)/(Complex.sin (φ w))^3) w := by
  have hder (z : ℂ) (hz : z ∈ U) : deriv φ z = complexPhaseSlope φ z := by
    apply phase_deriv_of_local_dispersion (hφ z hz).differentiableAt
    · exact Filter.eventually_of_mem (hU.mem_nhds hz) (fun z hz => hdisp z hz)
    · exact hsin z hz
  have heq : deriv φ =ᶠ[𝓝 w] complexPhaseSlope φ := by
    filter_upwards [hU.mem_nhds hw] with z hz
    exact hder z hz
  have hd := ((Complex.hasDerivAt_sin w).neg).div
    ((Complex.hasDerivAt_sin (φ w)).comp w (hφ w hw).differentiableAt.hasDerivAt)
    (hsin w hw)
  rw [hder w hw] at hd
  have hreduce := phase_curvature_quotient S (Complex.cos w) (Complex.sin w)
    (Complex.cos (φ w)) (Complex.sin (φ w)) (hsin w hw) (hdisp w hw)
    (Complex.sin_sq_add_cos_sq w) (Complex.sin_sq_add_cos_sq (φ w))
  change ((-Complex.cos w)*Complex.sin (φ w)-(-Complex.sin w)*
    (Complex.cos (φ w)*complexPhaseSlope φ w))/(Complex.sin (φ w))^2 = _ at hreduce
  simp only [Function.comp_apply, Pi.neg_apply] at hd
  rw [hreduce] at hd
  have hd' : HasDerivAt (complexPhaseSlope φ)
      (-S*(1-S*Complex.cos w+(Complex.cos w)^2)/(Complex.sin (φ w))^3) w := by
    convert! hd using 1
  exact hd'.congr_of_eventuallyEq heq


/-- Uniform positive numerator on the real reference right interval; the
lower bound is independent of the angular cosine. -/
theorem real_curvature_numerator_lower {S c : ℝ} (hS : 0 < S) (hS2 : S < 2) :
    0 < S*(1-S^2/4) ∧ S*(1-S^2/4) ≤ S*(1-S*c+c^2) := by
  constructor
  · have h : 0 < 1-S^2/4 := by nlinarith
    exact mul_pos hS h
  · apply mul_le_mul_of_nonneg_left _ hS.le
    nlinarith [sq_nonneg (c-S/2)]

/-- Algebraic form of the oblique cubic-sector estimate. The cone is wider
than the closed fourth-quadrant half-sector, allowing the small enlargement
used by the actual dispersion normal form. -/
theorem oblique_cube_polynomial_lower {c s x y : ℝ}
    (hc : 0 < c) (hsc : (12/5 : ℝ)*c ≤ s)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hyx : y ≤ (6/5 : ℝ)*x) :
    c*x^3 ≤ c*(x^3-3*x*y^2)+s*(3*x^2*y-y^3) := by
  have hs : 0 ≤ s := by linarith
  have hxy : x*y ≤ (6/5 : ℝ)*x^2 := by nlinarith [mul_nonneg hx (sub_nonneg.mpr hyx)]
  have hyy : y^2 ≤ (36/25 : ℝ)*x^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hyx) (show 0 ≤ (6/5 : ℝ)*x+y by positivity)]
  have hm1 := mul_le_mul_of_nonneg_left hxy (show 0 ≤ 3*c by positivity)
  have hm2 := mul_le_mul_of_nonneg_left hyy hs
  have hm3 := mul_le_mul_of_nonneg_right hsc (sq_nonneg x)
  have hbracket : 0 ≤ 3*s*x^2-3*c*x*y-s*y^2 := by
    nlinarith [mul_nonneg hc.le (sq_nonneg x)]
  have hmul := mul_nonneg hy hbracket
  nlinarith

/-- A quantitative reciprocal-cube sector estimate from the actual real and
imaginary coordinates. Its constant is uniform throughout the enlarged cone. -/
theorem oblique_inverse_cube_sector {c s x y : ℝ}
    (hc : 0 < c) (hsc : (12/5 : ℝ)*c ≤ s)
    (hx : 0 < x) (hy : 0 ≤ y) (hyx : y ≤ (6/5 : ℝ)*x) :
    (c/27) * ‖(((x : ℂ)-Complex.I*(y : ℂ))^3)⁻¹‖ ≤
      (((c : ℂ)-Complex.I*(s : ℂ))/((x : ℂ)-Complex.I*(y : ℂ))^3).re := by
  let z : ℂ := (x : ℂ)-Complex.I*(y : ℂ)
  have hz : z ≠ 0 := by
    intro h
    have hh := congrArg Complex.re h
    simp [z] at hh
    exact hx.ne' hh
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hnorm : ‖z‖ ≤ 3*x := by
    have h := Complex.norm_le_abs_re_add_abs_im z
    simp [z, abs_of_pos hx, abs_of_nonneg hy] at h
    linarith
  have hpow : ‖z‖^3 ≤ 27*x^3 := by
    have h := pow_le_pow_left₀ (norm_nonneg z) hnorm 3
    nlinarith
  have hpoly := oblique_cube_polynomial_lower hc hsc hx.le hy hyx
  have hre : (((c : ℂ)-Complex.I*(s : ℂ))/z^3).re =
      (c*(x^3-3*x*y^2)+s*(3*x^2*y-y^3))/(‖z‖^3)^2 := by
    rw [Complex.div_re, Complex.normSq_eq_norm_sq, norm_pow]
    simp only [z, pow_succ, pow_zero, Complex.mul_re, Complex.mul_im,
      Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.one_re, Complex.one_im]
    ring
  change (c/27)*‖(z^3)⁻¹‖ ≤ _
  rw [hre, norm_inv, norm_pow]
  apply (le_div_iff₀ (by positivity : 0 < (‖z‖^3)^2)).2
  have he : (c/27)*(‖z‖^3)⁻¹*(‖z‖^3)^2 = c/27*‖z‖^3 := by field_simp
  rw [he]
  nlinarith [mul_le_mul_of_nonneg_left hpow hc.le]


/-- The specific angle 3π/8 has the margin required for the enlarged
reciprocal-cube cone. The comparison is certified using the exact radicals. -/
theorem preferred_oblique_angle_margin :
    0 < Real.cos (3*Real.pi/8) ∧
      (12/5 : ℝ)*Real.cos (3*Real.pi/8) ≤ Real.sin (3*Real.pi/8) := by
  have hr0 := Real.sqrt_nonneg (2 : ℝ)
  have hr2 : (Real.sqrt (2 : ℝ))^2 = 2 := Real.sq_sqrt (by norm_num)
  have hrlt : Real.sqrt (2 : ℝ) < 2 := by nlinarith
  have hrmargin : (238/169 : ℝ) ≤ Real.sqrt 2 := by nlinarith
  have hminus : 0 < 2-Real.sqrt (2 : ℝ) := by linarith
  have hplus : 0 < 2+Real.sqrt (2 : ℝ) := by positivity
  have hm := Real.sq_sqrt hminus.le
  have hp := Real.sq_sqrt hplus.le
  have hm0 := Real.sqrt_nonneg (2-Real.sqrt (2 : ℝ))
  have hp0 := Real.sqrt_nonneg (2+Real.sqrt (2 : ℝ))
  rw [show 3*Real.pi/8 = Real.pi/2-Real.pi/8 by ring,
    Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub,
    Real.sin_pi_div_eight, Real.cos_pi_div_eight]
  constructor
  · exact div_pos (Real.sqrt_pos.2 hminus) (by norm_num)
  · nlinarith

/-- The actual source rotation in the quantitative inverse-cube estimate. -/
theorem preferred_oblique_inverse_cube {z : ℂ}
    (hzre : 0 < z.re) (hzim : z.im ≤ 0) (hcone : -z.im ≤ (6/5 : ℝ)*z.re) :
    (Real.cos (3*Real.pi/8)/27) * ‖(z^3)⁻¹‖ ≤
      (Complex.exp (-Complex.I*((3*Real.pi/8 : ℝ) : ℂ))/z^3).re := by
  have hz : (z.re : ℂ)-Complex.I*((-z.im : ℝ) : ℂ) = z := by
    apply Complex.ext <;> simp
  have he : Complex.exp (-Complex.I*((3*Real.pi/8 : ℝ) : ℂ)) =
      ((Real.cos (3*Real.pi/8) : ℝ) : ℂ) -
        Complex.I*((Real.sin (3*Real.pi/8) : ℝ) : ℂ) := by
    rw [show -Complex.I*((3*Real.pi/8 : ℝ) : ℂ) =
      ((-(3*Real.pi/8) : ℝ) : ℂ)*Complex.I by push_cast; ring,
      Complex.exp_ofReal_mul_I, Real.cos_neg, Real.sin_neg]
    push_cast
    ring
  have h := oblique_inverse_cube_sector preferred_oblique_angle_margin.1
    preferred_oblique_angle_margin.2 hzre (by linarith : 0 ≤ -z.im) hcone
  rw [hz, ← he] at h
  exact h

/-- The numerator at the physical lower branch equals sin²b exactly. -/
theorem branch_curvature_numerator (b : ℝ) :
    (1+Real.cos b)*(1-(1+Real.cos b)*Real.cos b+(Real.cos b)^2) =
      (Real.sin b)^2 := by
  have h := Real.sin_sq_add_cos_sq b
  nlinarith


/-- A small complex perturbation of the positive reference numerator
preserves a quantitative oblique projection of the full curvature quotient. -/
theorem preferred_curvature_numerator_perturbation {z Q : ℂ} {A : ℝ}
    (hA : 0 < A) (hzre : 0 < z.re) (hzim : z.im ≤ 0)
    (hcone : -z.im ≤ (6/5 : ℝ)*z.re)
    (hQ : ‖Q-(A : ℂ)‖ ≤ A*Real.cos (3*Real.pi/8)/54) :
    (Real.cos (3*Real.pi/8)/108)*‖Q/z^3‖ ≤
      (Complex.exp (-Complex.I*((3*Real.pi/8 : ℝ) : ℂ))*(Q/z^3)).re := by
  let c := Real.cos (3*Real.pi/8)
  let ω := Complex.exp (-Complex.I*((3*Real.pi/8 : ℝ) : ℂ))
  let L := ‖(z^3)⁻¹‖
  have hc : 0 < c := preferred_oblique_angle_margin.1
  have hz : z ≠ 0 := by
    intro h
    simp [h] at hzre
  have hL : 0 < L := norm_pos_iff.mpr (inv_ne_zero (pow_ne_zero 3 hz))
  have hω : ‖ω‖ ≤ 1 := by
    change ‖Complex.exp (-Complex.I*((3*Real.pi/8 : ℝ) : ℂ))‖ ≤ 1
    rw [Complex.norm_exp]
    simp only [Complex.mul_re, Complex.neg_re, Complex.I_re, Complex.ofReal_im]
    norm_num
  have hsector : c/27*L ≤ (ω/z^3).re := preferred_oblique_inverse_cube hzre hzim hcone
  have hreB : (ω*((A : ℂ)*(z^3)⁻¹)).re = A*(ω/z^3).re := by
    rw [show ω*((A : ℂ)*(z^3)⁻¹) = (A : ℂ)*(ω/z^3) by
      simp only [div_eq_mul_inv]; ring]
    simp
  have hbase : (A*c/27)*L ≤ (ω*((A : ℂ)*(z^3)⁻¹)).re := by
    rw [hreB]
    nlinarith [mul_le_mul_of_nonneg_left hsector hA.le]
  have herr : ‖(Q-(A : ℂ))*(z^3)⁻¹‖ ≤ (A*c/27)*L/2 := by
    rw [norm_mul]
    have h := mul_le_mul_of_nonneg_right hQ hL.le
    change ‖Q-(A : ℂ)‖*L ≤ _
    dsimp [c] at h ⊢
    nlinarith
  have hproj := (oblique_correction_absorption
    (show 0 < A*c/27 by positivity) hL hω hbase herr).1
  have he : (A : ℂ)*(z^3)⁻¹ + (Q-(A : ℂ))*(z^3)⁻¹ = Q/z^3 := by
    simp only [div_eq_mul_inv]
    ring
  rw [he] at hproj
  have hQnorm : ‖Q‖ ≤ 2*A := by
    have hcos := Real.cos_le_one (3*Real.pi/8)
    calc
      ‖Q‖ = ‖(Q-(A : ℂ))+(A : ℂ)‖ := by congr 1; ring
      _ ≤ ‖Q-(A : ℂ)‖+‖(A : ℂ)‖ := norm_add_le _ _
      _ = ‖Q-(A : ℂ)‖+A := by simp [abs_of_pos hA]
      _ ≤ 2*A := by nlinarith [mul_le_mul_of_nonneg_left hcos hA.le]
  have hcurv : ‖Q/z^3‖ ≤ 2*A*L := by
    rw [norm_div, div_eq_mul_inv]
    simpa only [L, norm_inv] using mul_le_mul_of_nonneg_right hQnorm hL.le
  change c/108*‖Q/z^3‖ ≤ (ω*(Q/z^3)).re
  calc
    c/108*‖Q/z^3‖ ≤ c/108*(2*A*L) :=
      mul_le_mul_of_nonneg_left hcurv (by positivity)
    _ ≤ _ := by nlinarith


/-- Radial trace appearing in the exact Preferred dispersion. -/
def outwardRadialTrace (d : PreferredBranchData) (ε : ℝ) : ℂ :=
  IsingBulk.Branch.radialParameter d.alpha ε +
    (IsingBulk.Branch.radialParameter d.alpha ε)⁻¹

/-- The actual twice-differentiated dispersion numerator on the outward plateau. -/
def outwardCurvatureNumerator (d : PreferredBranchData) (ε δ u : ℝ) : ℂ :=
  outwardRadialTrace d ε * (1-outwardRadialTrace d ε *
    Complex.cos (outwardPlateauAngle d δ u)+(Complex.cos (outwardPlateauAngle d δ u))^2)

def outwardCurvature (d : PreferredBranchData) (ε δ u : ℝ) : ℂ :=
  outwardCurvatureNumerator d ε δ u/(Complex.sin (outwardPlateauPhase d ε δ u))^3

theorem outwardRadialTrace_zero (d : PreferredBranchData) :
    outwardRadialTrace d 0 = ((1+Real.cos d.b : ℝ) : ℂ) := by
  obtain ⟨hr,hi⟩ := IsingBulk.Branch.radial_trace_components d.alpha 0 (by norm_num)
  apply Complex.ext
  · change (IsingBulk.Branch.radialParameter d.alpha 0+
      (IsingBulk.Branch.radialParameter d.alpha 0)⁻¹).re = _
    rw [hr]
    simp only [Complex.ofReal_re]
    rw [d.angle_relation]
    ring
  · change (IsingBulk.Branch.radialParameter d.alpha 0+
      (IsingBulk.Branch.radialParameter d.alpha 0)⁻¹).im = _
    rw [hi]
    simp

theorem outwardCurvatureNumerator_zero (d : PreferredBranchData) :
    outwardCurvatureNumerator d 0 0 0 = (((Real.sin d.b)^2 : ℝ) : ℂ) := by
  unfold outwardCurvatureNumerator
  rw [outwardRadialTrace_zero]
  simp only [outwardPlateauAngle, Complex.ofReal_zero, mul_zero, sub_zero, add_zero,
    Complex.ofReal_neg, Complex.cos_neg, ← Complex.ofReal_cos]
  norm_cast
  exact branch_curvature_numerator d.b

theorem outwardCurvatureNumerator_continuous (d : PreferredBranchData) :
    ContinuousAt (fun z : ℝ × ℝ × ℝ => outwardCurvatureNumerator d z.1 z.2.1 z.2.2) 0 := by
  unfold outwardCurvatureNumerator outwardRadialTrace outwardPlateauAngle
    IsingBulk.Branch.radialParameter
  fun_prop (disch := simp [Complex.exp_ne_zero])

/-- The source curvature numerator is uniformly close to its positive branch
value in an actual parameter cube, without a relation between δ and ε. -/
theorem outward_curvature_numerator_small (d : PreferredBranchData) :
    ∃ r : ℝ, 0 < r ∧ ∀ ε δ u : ℝ, |ε| < r → |δ| < r → |u| < r →
      ‖outwardCurvatureNumerator d ε δ u-(((Real.sin d.b)^2 : ℝ):ℂ)‖ ≤
        (Real.sin d.b)^2*Real.cos (3*Real.pi/8)/54 := by
  have hA : 0 < (Real.sin d.b)^2 :=
    sq_pos_of_pos (Real.sin_pos_of_pos_of_lt_pi d.b_pos d.b_lt)
  have hc := preferred_oblique_angle_margin.1
  have he : ∀ᶠ z : ℝ × ℝ × ℝ in 𝓝 0,
      ‖outwardCurvatureNumerator d z.1 z.2.1 z.2.2-
        (((Real.sin d.b)^2 : ℝ):ℂ)‖ < (Real.sin d.b)^2*Real.cos (3*Real.pi/8)/54 := by
    have hcont := ((outwardCurvatureNumerator_continuous d).sub_const
      (((Real.sin d.b)^2 : ℝ):ℂ)).norm
    apply hcont.eventually_lt continuousAt_const
    change ‖outwardCurvatureNumerator d 0 0 0-(((Real.sin d.b)^2 : ℝ):ℂ)‖ < _
    rw [outwardCurvatureNumerator_zero, sub_self, norm_zero]
    positivity
  obtain ⟨r,hr,hball⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨r,hr,?_⟩
  intro ε δ u hε hδ hu
  apply (hball (y := (ε,δ,u)) ?_).le
  simpa only [dist_zero_right, Prod.norm_def, Real.norm_eq_abs, max_lt_iff] using
    And.intro hε (And.intro hδ hu)

/-- A quantitative oblique curvature cone on the actual Preferred outward
plateau, uniform up to u=0 and δ=0.  No coarea estimate is assumed. -/
theorem preferred_outward_curvature_cone (d : PreferredBranchData) :
    ∃ r : ℝ, 0 < r ∧ ∀ ε δ u : ℝ,
      0 < ε → ε < r → 0 ≤ δ → δ < r → 0 ≤ u → u < r →
      (Real.cos (3*Real.pi/8)/108)*‖outwardCurvature d ε δ u‖ ≤
        (Complex.exp (-Complex.I*((3*Real.pi/8 : ℝ):ℂ))*outwardCurvature d ε δ u).re := by
  obtain ⟨_,_,r₁,_,_,hr₁,hbranch⟩ := preferred_outward_branch_control d
  obtain ⟨r₂,hr₂,hnum⟩ := outward_curvature_numerator_small d
  refine ⟨min r₁ r₂,lt_min hr₁ hr₂,?_⟩
  intro ε δ u hε hεr hδ hδr hu hur
  obtain ⟨_,_,hzr,hzi,hcone,_⟩ := hbranch ε δ u hε
    (hεr.trans_le (min_le_left _ _)) hδ (hδr.trans_le (min_le_left _ _))
    hu (hur.trans_le (min_le_left _ _))
  have hQ := hnum ε δ u
    (by simpa only [abs_of_pos hε] using hεr.trans_le (min_le_right r₁ r₂))
    (by simpa only [abs_of_nonneg hδ] using hδr.trans_le (min_le_right r₁ r₂))
    (by simpa only [abs_of_nonneg hu] using hur.trans_le (min_le_right r₁ r₂))
  exact preferred_curvature_numerator_perturbation
    (sq_pos_of_pos (Real.sin_pos_of_pos_of_lt_pi d.b_pos d.b_lt)) hzr (by linarith) hcone hQ


/-- The phase curvature quotient is exactly the negative second real angular
derivative on its physical quadrant. Only regularity of this actual branch is
required; all plateau parameters are fixed in this derivative. -/
theorem outwardPhase_second_hasDerivAt (d : PreferredBranchData) (ε δ u : ℝ)
    (hwr : 0 < (outwardPlateauW d ε δ u).re)
    (hwi : 0 < (outwardPlateauW d ε δ u).im) :
    HasDerivAt (deriv (outwardPlateauPhase d ε δ)) (-outwardCurvature d ε δ u) u := by
  let t := δ+d.localData.c₀*ε
  have hr : 0 < (IsingBulk.Branch.currentW d.localData ε t u).re := by
    simpa only [t, outwardPlateauW_transfer] using hwr
  have hi : 0 < (IsingBulk.Branch.currentW d.localData ε t u).im := by
    simpa only [t, outwardPlateauW_transfer] using hwi
  have hphase : IsingBulk.Branch.currentPhase d.localData ε t =
      outwardPlateauPhase d ε δ := funext (outwardPlateauPhase_transfer d ε δ)
  have hshift : -d.localData.c₀*ε+d.localData.tau*t/2 = δ := by
    change -d.localData.c₀*ε+2*(δ+d.localData.c₀*ε)/2 = δ
    ring
  have harg : (δ:ℂ)+(-(d.b:ℂ)+(u:ℂ))*Complex.I =
      outwardPlateauAngle d δ u*Complex.I := by
    unfold outwardPlateauAngle
    push_cast
    ring_nf
    simp [Complex.I_sq]
  have hdu : IsingBulk.Branch.currentDu d.localData ε t u =
      -Complex.sin (outwardPlateauAngle d δ u) := by
    unfold IsingBulk.Branch.currentDu
    rw [hshift]
    change Complex.sinh ((δ:ℂ)+(-(d.b:ℂ)+(u:ℂ))*Complex.I)*Complex.I = _
    rw [harg, Complex.sinh_mul_I]
    ring_nf
    simp [Complex.I_sq]
  have hduu : IsingBulk.Branch.currentDuu d.localData ε t u =
      -Complex.cos (outwardPlateauAngle d δ u) := by
    unfold IsingBulk.Branch.currentDuu
    rw [hshift]
    change -Complex.cosh ((δ:ℂ)+(-(d.b:ℂ)+(u:ℂ))*Complex.I) = _
    rw [harg, Complex.cosh_mul_I]
  have hn : Complex.sin (outwardPlateauPhase d ε δ u) ≠ 0 := by
    rw [← hphase]
    exact IsingBulk.Branch.current_phase_sin_ne_zero d.localData ε t u hr hi
  have hd := IsingBulk.Branch.currentPhase_second_hasDerivAt d.localData ε t u hr hi
  rw [hphase, hdu, hduu, show IsingBulk.Branch.currentW d.localData ε t u =
    outwardPlateauW d ε δ u from outwardPlateauW_transfer d ε δ u] at hd
  have hp : (Complex.sin (outwardPlateauPhase d ε δ u))^2+
      (outwardPlateauW d ε δ u)^2 = 1 := by
    rw [← outwardPlateauPhase_cos]
    exact Complex.sin_sq_add_cos_sq _
  have hc := phase_curvature_quotient (outwardRadialTrace d ε)
    (Complex.cos (outwardPlateauAngle d δ u)) (Complex.sin (outwardPlateauAngle d δ u))
    (outwardPlateauW d ε δ u) (Complex.sin (outwardPlateauPhase d ε δ u)) hn
    (outwardPlateauW_formula d ε δ u) (Complex.sin_sq_add_cos_sq _) hp
  have he : -Complex.cos (outwardPlateauAngle d δ u)/Complex.sin (outwardPlateauPhase d ε δ u)-
      (-Complex.sin (outwardPlateauAngle d δ u))^2*outwardPlateauW d ε δ u/
        (Complex.sin (outwardPlateauPhase d ε δ u))^3 =
      -outwardCurvature d ε δ u := by
    unfold outwardCurvature outwardCurvatureNumerator
    rw [show -(outwardRadialTrace d ε * (1-outwardRadialTrace d ε*
        Complex.cos (outwardPlateauAngle d δ u)+(Complex.cos (outwardPlateauAngle d δ u))^2)/
          (Complex.sin (outwardPlateauPhase d ε δ u))^3) =
        -outwardRadialTrace d ε * (1-outwardRadialTrace d ε*
        Complex.cos (outwardPlateauAngle d δ u)+(Complex.cos (outwardPlateauAngle d δ u))^2)/
          (Complex.sin (outwardPlateauPhase d ε δ u))^3 by ring]
    rw [← hc]
    field_simp
  rw [he] at hd
  exact hd


/-- A small numerator perturbation gives its needed two-sided size bounds. -/
theorem curvature_numerator_norm_bounds {Q : ℂ} {A : ℝ} (hA : 0 < A)
    (hQ : ‖Q-(A:ℂ)‖ ≤ A*Real.cos (3*Real.pi/8)/54) :
    A/2 ≤ ‖Q‖ ∧ ‖Q‖ ≤ 2*A := by
  have hcos := Real.cos_le_one (3*Real.pi/8)
  have herr : ‖Q-(A:ℂ)‖ ≤ A/2 := by
    nlinarith [mul_le_mul_of_nonneg_left hcos hA.le]
  have hlo : A ≤ ‖Q-(A:ℂ)‖+‖Q‖ := by
    calc
      A = ‖(A:ℂ)‖ := by simp [abs_of_pos hA]
      _ = ‖-(Q-(A:ℂ))+Q‖ := by congr 1; ring
      _ ≤ ‖-(Q-(A:ℂ))‖+‖Q‖ := norm_add_le _ _
      _ = ‖Q-(A:ℂ)‖+‖Q‖ := by rw [norm_neg]
  have hhi : ‖Q‖ ≤ ‖Q-(A:ℂ)‖+A := by
    calc
      ‖Q‖ = ‖(Q-(A:ℂ))+(A:ℂ)‖ := by congr 1; ring
      _ ≤ ‖Q-(A:ℂ)‖+‖(A:ℂ)‖ := norm_add_le _ _
      _ = ‖Q-(A:ℂ)‖+A := by simp [abs_of_pos hA]
  constructor <;> linarith

theorem sqrt_cube_eq_three_halves {x : ℝ} (hx : 0 < x) :
    (Real.sqrt x)^3 = x^(3/2:ℝ) := by
  calc
    (Real.sqrt x)^3 = x*Real.sqrt x := by rw [pow_succ, Real.sq_sqrt hx.le]
    _ = x^((1:ℝ)+(1/2:ℝ)) := by
      rw [Real.rpow_add hx, Real.rpow_one, ← Real.sqrt_eq_rpow]
    _ = x^(3/2:ℝ) := by congr 1; norm_num

/-- Converting the actual sine square-root bounds and numerator size to the
inverse-three-halves curvature scale is an exact numerical step. -/
theorem cubic_quotient_scale {Q z : ℂ} {a A c C L : ℝ}
    (hL : 0 < L) (hc : 0 < c) (hA : 0 ≤ A)
    (hQlo : a ≤ ‖Q‖) (hQhi : ‖Q‖ ≤ A)
    (hzlo : c*Real.sqrt L ≤ ‖z‖) (hzhi : ‖z‖ ≤ C*Real.sqrt L) :
    (a/C^3)*L^(-(3/2:ℝ)) ≤ ‖Q/z^3‖ ∧
      ‖Q/z^3‖ ≤ (A/c^3)*L^(-(3/2:ℝ)) := by
  have hzpos : 0 < ‖z‖ := (mul_pos hc (Real.sqrt_pos.mpr hL)).trans_le hzlo
  have hpowlo := pow_le_pow_left₀ (by positivity : 0 ≤ c*Real.sqrt L) hzlo 3
  have hpowhi := pow_le_pow_left₀ (norm_nonneg z) hzhi 3
  have he (q t : ℝ) : q/(t*Real.sqrt L)^3 = (q/t^3)*L^(-(3/2:ℝ)) := by
    rw [mul_pow, sqrt_cube_eq_three_halves hL, Real.rpow_neg hL.le]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  have hlo := div_le_div₀ (norm_nonneg Q) hQlo (pow_pos hzpos 3) hpowhi
  have hhi := div_le_div₀ hA hQhi (pow_pos (mul_pos hc (Real.sqrt_pos.mpr hL)) 3) hpowlo
  rw [he] at hlo hhi
  simpa only [norm_div, norm_pow] using And.intro hlo hhi

/-- The actual outward curvature has its complete inverse-three-halves
scale and a uniform quantitative lower oblique projection. This includes
all nonnegative outward shifts sufficiently close to the physical branch. -/
theorem preferred_outward_curvature_scale (d : PreferredBranchData) :
    ∃ c C r : ℝ, 0 < c ∧ 0 < C ∧ 0 < r ∧ ∀ ε δ u : ℝ,
      0 < ε → ε < r → 0 ≤ δ → δ < r → 0 ≤ u → u < r →
      c*(u+ε+δ)^(-(3/2:ℝ)) ≤ ‖outwardCurvature d ε δ u‖ ∧
      ‖outwardCurvature d ε δ u‖ ≤ C*(u+ε+δ)^(-(3/2:ℝ)) ∧
      (Real.cos (3*Real.pi/8)/108*c)*(u+ε+δ)^(-(3/2:ℝ)) ≤
        (Complex.exp (-Complex.I*((3*Real.pi/8:ℝ):ℂ))*outwardCurvature d ε δ u).re := by
  obtain ⟨c,C,r₁,hc,hC,hr₁,hbranch⟩ := preferred_outward_branch_control d
  obtain ⟨r₂,hr₂,hnum⟩ := outward_curvature_numerator_small d
  let A := (Real.sin d.b)^2
  have hA : 0 < A := sq_pos_of_pos (Real.sin_pos_of_pos_of_lt_pi d.b_pos d.b_lt)
  refine ⟨(A/2)/C^3,(2*A)/c^3,min r₁ r₂,by positivity,by positivity,
    lt_min hr₁ hr₂,?_⟩
  intro ε δ u hε hεr hδ hδr hu hur
  obtain ⟨hzlo,hzhi,hzr,hzi,hcone,_⟩ := hbranch ε δ u hε
    (hεr.trans_le (min_le_left _ _)) hδ (hδr.trans_le (min_le_left _ _))
    hu (hur.trans_le (min_le_left _ _))
  have hQ := hnum ε δ u
    (by simpa only [abs_of_pos hε] using hεr.trans_le (min_le_right r₁ r₂))
    (by simpa only [abs_of_nonneg hδ] using hδr.trans_le (min_le_right r₁ r₂))
    (by simpa only [abs_of_nonneg hu] using hur.trans_le (min_le_right r₁ r₂))
  obtain ⟨hQlo,hQhi⟩ := curvature_numerator_norm_bounds hA hQ
  obtain ⟨hlo,hhi⟩ := cubic_quotient_scale (by positivity : 0 < u+ε+δ) hc
    (by positivity : 0 ≤ 2*A) hQlo hQhi hzlo hzhi
  have hproj := preferred_curvature_numerator_perturbation hA hzr (by linarith) hcone hQ
  refine ⟨hlo,hhi,?_⟩
  have hcos := preferred_oblique_angle_margin.1
  have hmul := mul_le_mul_of_nonneg_left hlo (by positivity : 0 ≤ Real.cos (3*Real.pi/8)/108)
  change _ ≤ (Complex.exp (-Complex.I*((3*Real.pi/8:ℝ):ℂ))*
    (outwardCurvatureNumerator d ε δ u/(Complex.sin (outwardPlateauPhase d ε δ u))^3)).re
  nlinarith


/-- Integrating the comparison curvature by a proved antiderivative gives
the exact rational extreme gap; the comparison is made at fixed parameters. -/
theorem projected_gap_of_deriv_upper {g g' : ℝ → ℝ} {m M E k : ℝ}
    (hmE : 0 < m+E) (hmM : m ≤ M)
    (hg : ∀ u ∈ Icc m M, HasDerivAt g (g' u) u)
    (hbound : ∀ u ∈ Icc m M, g' u ≤ -k*(u+E)^(-(3/2:ℝ))) :
    k*(2*(M-m)/(Real.sqrt (m+E)*Real.sqrt (M+E)*
      (Real.sqrt (m+E)+Real.sqrt (M+E)))) ≤ g m-g M := by
  let F := fun u : ℝ => g u+k*(-2*(u+E)^(-(1/2:ℝ)))
  have hpos (u : ℝ) (hu : u ∈ Icc m M) : 0 < u+E := by linarith [hu.1]
  have hprimitive (u : ℝ) (hu : u ∈ Icc m M) :
      HasDerivAt (fun v : ℝ => -2*(v+E)^(-(1/2:ℝ))) ((u+E)^(-(3/2:ℝ))) u := by
    have h := (((hasDerivAt_id u).add_const E).rpow_const
      (p := -(1/2:ℝ)) (Or.inl (hpos u hu).ne')).const_mul (-2)
    convert h using 1
    norm_num
    ring_nf
    simp only [id_eq, add_comm]
  have hF (u : ℝ) (hu : u ∈ Icc m M) :
      HasDerivAt F (g' u+k*(u+E)^(-(3/2:ℝ))) u :=
    (hg u hu).add ((hprimitive u hu).const_mul k)
  have hanti : AntitoneOn F (Icc m M) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc m M)
    · intro u hu
      exact (hF u hu).continuousAt.continuousWithinAt
    · intro u hu
      exact (hF u (interior_subset hu)).differentiableAt.differentiableWithinAt
    · intro u hu
      rw [(hF u (interior_subset hu)).deriv]
      linarith [hbound u (interior_subset hu)]
  have hdrop := hanti (left_mem_Icc.mpr hmM) (right_mem_Icc.mpr hmM) hmM
  have hME : 0 < M+E := by linarith
  have hrat := inverse_sqrt_difference hmE hME
  have hpow (x : ℝ) (hx : 0 < x) : x^(-(1/2:ℝ)) = (Real.sqrt x)⁻¹ := by
    rw [Real.rpow_neg hx.le, ← Real.sqrt_eq_rpow]
  dsimp [F] at hdrop
  rw [hpow _ hmE, hpow _ hME] at hdrop
  rw [show M+E-(m+E) = M-m by ring] at hrat
  rw [← hrat]
  simp only [div_eq_mul_inv] at hdrop ⊢
  nlinarith

/-- Source (G4) on the actual outward plateau. The phase is the explicit
physical branch and the entire derivative gap follows from its derived
curvature, including the endpoint m=0. -/
theorem preferred_outward_extreme_gap (d : PreferredBranchData) :
    ∃ k r : ℝ, 0 < k ∧ 0 < r ∧ ∀ ε δ m M : ℝ,
      0 < ε → ε < r → 0 ≤ δ → δ < r → 0 ≤ m → m ≤ M → M < r →
      k*(2*(M-m)/(Real.sqrt (m+ε+δ)*Real.sqrt (M+ε+δ)*
        (Real.sqrt (m+ε+δ)+Real.sqrt (M+ε+δ)))) ≤
      (Complex.exp (-Complex.I*((3*Real.pi/8:ℝ):ℂ))*
        (deriv (outwardPlateauPhase d ε δ) m-deriv (outwardPlateauPhase d ε δ) M)).re := by
  obtain ⟨c,_,r₁,hc,_,hr₁,hscale⟩ := preferred_outward_curvature_scale d
  obtain ⟨r₂,hr₂,hdomain⟩ := preferred_outward_branch_domain d
  let k := Real.cos (3*Real.pi/8)/108*c
  have hk : 0 < k := by dsimp [k]; have := preferred_oblique_angle_margin.1; positivity
  let ω := Complex.exp (-Complex.I*((3*Real.pi/8:ℝ):ℂ))
  refine ⟨k,min r₁ r₂,hk,lt_min hr₁ hr₂,?_⟩
  intro ε δ m M hε hεr hδ hδr hm hmM hMr
  let g := fun u : ℝ => (ω*deriv (outwardPlateauPhase d ε δ) u).re
  let g' := fun u : ℝ => -(ω*outwardCurvature d ε δ u).re
  have hu (u : ℝ) (h : u ∈ Icc m M) : 0 ≤ u ∧ u < min r₁ r₂ :=
    ⟨hm.trans h.1,h.2.trans_lt hMr⟩
  have hg (u : ℝ) (h : u ∈ Icc m M) : HasDerivAt g (g' u) u := by
    have hup := hu u h
    obtain ⟨hwr,hwi⟩ := hdomain ε δ u hε (hεr.trans_le (min_le_right _ _))
      hδ (hδr.trans_le (min_le_right _ _))
      (by simpa only [abs_of_nonneg hup.1] using hup.2.trans_le (min_le_right r₁ r₂))
    have hd := (outwardPhase_second_hasDerivAt d ε δ u hwr hwi).const_mul ω
    have hre := Complex.reCLM.hasFDerivAt.comp_hasDerivAt u hd
    simpa [g,g',Function.comp_def] using hre
  have hbound (u : ℝ) (h : u ∈ Icc m M) :
      g' u ≤ -k*(u+(ε+δ))^(-(3/2:ℝ)) := by
    have hup := hu u h
    obtain ⟨_,_,hproj⟩ := hscale ε δ u hε (hεr.trans_le (min_le_left _ _))
      hδ (hδr.trans_le (min_le_left _ _)) hup.1 (hup.2.trans_le (min_le_left _ _))
    change k*(u+ε+δ)^(-(3/2:ℝ)) ≤ (ω*outwardCurvature d ε δ u).re at hproj
    dsimp [g']
    rw [← add_assoc]
    linarith
  have hgap := projected_gap_of_deriv_upper (E := ε+δ) (by positivity) hmM hg hbound
  simpa only [g,ω,← add_assoc, mul_sub, Complex.sub_re] using hgap


/-- The genuine occupancy sums retain their particle-count factor, which is
then cancelled by the 1/N in the actual balanced-contour Jacobian. -/
theorem occupancy_sum_norm_bound {ι : Type*} [Fintype ι]
    {p b : ι → ℂ} {A : ℝ} (hp : ∀ i, ‖p i‖ ≤ 1) (hb : ∀ i, ‖b i‖ ≤ A) :
    ‖∑ i, p i*b i‖ ≤ (Fintype.card ι:ℝ)*A := by
  calc
    ‖∑ i, p i*b i‖ ≤ ∑ i, ‖p i*b i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : ι, A := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_mul]
      calc
        ‖p i‖*‖b i‖ ≤ 1*‖b i‖ := mul_le_mul_of_nonneg_right (hp i) (norm_nonneg _)
        _ ≤ A := by simpa using hb i
    _ = _ := by simp

/-- Full occupancy correction in G5, with the particle factor cancelled.
The input bounds concern the actual slopes at this configuration and the
two actual bump-derivative differences, not a path of permuted extrema. -/
theorem actual_occupancy_correction_norm {N : ℕ} (hN : 0 < N)
    {τ K d A : ℝ} (hτ : 0 ≤ τ) (hK : 0 ≤ K) (hd : 0 ≤ d) (_hA : 0 ≤ A)
    {p m b : Fin N → ℂ} {dp dm : ℂ}
    (hp : ∀ i, ‖p i‖ ≤ 1) (hm : ∀ i, ‖m i‖ ≤ 1) (hb : ∀ i, ‖b i‖ ≤ A)
    (hdp : ‖dp‖ ≤ K*d) (hdm : ‖dm‖ ≤ K*d) :
    ‖-(Complex.I*(τ:ℂ)/(N:ℂ))*dp*(∑ i, m i*b i)+
      (Complex.I*(τ:ℂ)/(N:ℂ))*dm*(∑ i, p i*b i)‖ ≤ 2*τ*K*d*A := by
  let κ : ℂ := Complex.I*(τ:ℂ)/(N:ℂ)
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  have hκ : ‖κ‖ = τ/(N:ℝ) := by
    dsimp [κ]
    rw [norm_div, norm_mul, Complex.norm_I, one_mul]
    simp [abs_of_nonneg hτ]
  have hBm : ‖∑ i, m i*b i‖ ≤ (N:ℝ)*A := by
    simpa only [Fintype.card_fin] using occupancy_sum_norm_bound hm hb
  have hBp : ‖∑ i, p i*b i‖ ≤ (N:ℝ)*A := by
    simpa only [Fintype.card_fin] using occupancy_sum_norm_bound hp hb
  have hterm {q B : ℂ} (hq : ‖q‖ ≤ K*d) (hB : ‖B‖ ≤ (N:ℝ)*A) :
      ‖κ*q*B‖ ≤ τ*K*d*A := by
    calc
      ‖κ*q*B‖ = (τ/(N:ℝ))*‖q‖*‖B‖ := by rw [norm_mul, norm_mul, hκ]
      _ ≤ (τ/(N:ℝ))*(K*d)*((N:ℝ)*A) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hq (by positivity)) hB
          (norm_nonneg _) (by positivity)
      _ = τ*K*d*A := by field_simp
  calc
    _ = ‖-(κ*dp*(∑ i, m i*b i))+(κ*dm*(∑ i, p i*b i))‖ := by
      congr 1
      dsimp [κ]
      ring
    _ ≤ ‖-(κ*dp*(∑ i, m i*b i))‖+‖κ*dm*(∑ i, p i*b i)‖ := norm_add_le _ _
    _ = ‖κ*dp*(∑ i, m i*b i)‖+‖κ*dm*(∑ i, p i*b i)‖ := by rw [norm_neg]
    _ ≤ 2*τ*K*d*A := by linarith [hterm hdp hBm, hterm hdm hBp]

/-- The correction's d/sqrt(m+E) factor is controlled by the exact G4
comparison integral on every bounded right interval, with no transposition path. -/
theorem occupancy_correction_scale {x y R : ℝ}
    (hx : 0 < x) (hxy : x ≤ y) (hyR : y ≤ R) :
    (y-x)/Real.sqrt x ≤ R*(2*(y-x)/
      (Real.sqrt x*Real.sqrt y*(Real.sqrt x+Real.sqrt y))) := by
  have hy : 0 < y := hx.trans_le hxy
  have hsx := Real.sqrt_pos.mpr hx
  have hsy := Real.sqrt_pos.mpr hy
  have hsxy := Real.sqrt_le_sqrt hxy
  have hden : 0 < Real.sqrt x*Real.sqrt y*(Real.sqrt x+Real.sqrt y) := by positivity
  rw [← mul_div_assoc]
  apply (le_div_iff₀ hden).mpr
  have he : (y-x)/Real.sqrt x*(Real.sqrt x*Real.sqrt y*(Real.sqrt x+Real.sqrt y)) =
      (y-x)*(Real.sqrt y*(Real.sqrt x+Real.sqrt y)) := by field_simp
  rw [he]
  have hmid : Real.sqrt y*(Real.sqrt x+Real.sqrt y) ≤ 2*R := by
    nlinarith [Real.sq_sqrt hy.le, mul_le_mul_of_nonneg_left hsxy hsy.le]
  nlinarith [mul_le_mul_of_nonneg_left hmid (sub_nonneg.mpr hxy)]


/-- The occupancy energy is controlled by the actual maximum, because
positive p-occupancy forces a real angle into p's one-sided support. -/
theorem actual_occupancy_energy_comparison {N : ℕ} (hN : 0 < N)
    {p u : Fin N → ℝ} {b τ ε M : ℝ}
    (hb : 0 < b) (hτ : 0 ≤ τ) (hε : 0 ≤ ε) (hM : 0 ≤ M)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (humax : ∀ i, u i ≤ M) (hsupport : ∀ i, 0 < p i → b ≤ u i) :
    ε+τ*((∑ i, p i)/(N:ℝ)) ≤ (1+τ/b)*(M+ε) := by
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  have hsum : (∑ i, p i) ≤ (N:ℝ) := by
    calc
      (∑ i, p i) ≤ ∑ _i : Fin N, (1:ℝ) := Finset.sum_le_sum (fun i _ => hp1 i)
      _ = _ := by simp
  have hσ : (∑ i, p i)/(N:ℝ) ≤ 1 :=
    (div_le_iff₀ hNr).mpr (by simpa using hsum)
  have hτb : 0 ≤ τ/b := div_nonneg hτ hb.le
  by_cases hP : (∑ i, p i) = 0
  · rw [hP, zero_div, mul_zero, add_zero]
    nlinarith [mul_nonneg hτb (add_nonneg hM hε)]
  · have hex : ∃ i, 0 < p i := by
      by_contra h
      push Not at h
      have he : ∀ i, p i = 0 := fun i => le_antisymm (h i) (hp0 i)
      apply hP
      simp [he]
    obtain ⟨i,hi⟩ := hex
    have hbM : b ≤ M := (hsupport i hi).trans (humax i)
    have hτM : τ ≤ (τ/b)*M := by
      calc
        τ = (τ/b)*b := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left hbM hτb
    have he : ε+τ ≤ (1+τ/b)*(M+ε) := by
      nlinarith [mul_nonneg hτb hε]
    exact (by nlinarith [mul_le_mul_of_nonneg_left hσ hτ] :
      ε+τ*((∑ i, p i)/(N:ℝ)) ≤ ε+τ).trans he

/-- The actual angular extreme fiber after the constraint eliminates the
maximum M=A−m. Smooth cutoff supports are deliberately absent: after taking
absolute values the geometric right rectangle gives these interval conditions. -/
def extremeShellFiber {ι : Type*} (A r lo hi : ℝ) (others : ι → ℝ) : Set ℝ :=
  {m | lo ≤ m ∧ A-m ≤ hi ∧ m ≤ A-m ∧ r ≤ A-2*m ∧ A-2*m ≤ 2*r ∧
    ∀ i, m ≤ others i ∧ others i ≤ A-m}

/-- The extreme fiber is one interval (possibly empty), uniformly in the
fixed remaining angles. No component count for a smooth bump fiber is assumed. -/
theorem extremeShellFiber_ordConnected {ι : Type*}
    (A r lo hi : ℝ) (others : ι → ℝ) :
    Set.OrdConnected (extremeShellFiber A r lo hi others) := by
  apply Set.ordConnected_iff.mpr
  intro x hx y hy _ z hz
  rcases hx with ⟨hx0,hx1,hx2,hx3,hx4,hx5⟩
  rcases hy with ⟨hy0,hy1,hy2,hy3,hy4,hy5⟩
  refine ⟨by linarith [hz.1],by linarith [hz.1],by linarith [hz.2],
    by linarith [hz.2],by linarith [hz.1],?_⟩
  intro i
  have hyi := hy5 i
  constructor <;> linarith [hz.2]


/-- Concrete smooth one-sided periodic bump data from §5. These are the
source support and plateau conditions, with no coarea or tail estimate as a field. -/
structure PreferredCoareaBump (d : PreferredBranchData) where
  delta : ℝ
  delta_pos : 0 < delta
  delta_alpha : delta < d.alpha/2
  delta_b : delta < d.b/2
  delta_gap : delta < (2*d.alpha-d.b)/2
  branch_plateau : d.b < Real.pi-delta
  p : ℝ → ℝ
  smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) p
  periodic : Function.Periodic p (2*Real.pi)
  lower_bound : ∀ θ, 0 ≤ p θ
  upper_bound : ∀ θ, p θ ≤ 1
  upper_support : ∀ θ ∈ Icc (-Real.pi) Real.pi, p θ ≠ 0 → θ ∈ Ioo 0 Real.pi
  plateau : ∀ θ ∈ Icc delta (Real.pi-delta), p θ = 1

def PreferredCoareaBump.m {d : PreferredBranchData} (B : PreferredCoareaBump d)
    (θ : ℝ) : ℝ := B.p (-θ)

/-- The actual logarithmic physical angular phase used in G(θ). -/
def preferredAngularPhase (d : PreferredBranchData) (ε : ℝ) (w : ℂ) : ℂ :=
  preferredArccos (outwardRadialTrace d ε-Complex.cos w)

def preferredTotalPhase {N : ℕ} (d : PreferredBranchData) (ε τ : ℝ)
    (p m : ℝ → ℝ) (θ : Fin N → ℝ) : ℂ :=
  ∑ i, preferredAngularPhase d ε (deformedAngles τ p m θ i)

/-- This affine path moves only the actual two extreme angles and preserves
the constrained sum at every parameter value. -/
def extremeAnglePath {N : ℕ} (θ : Fin N → ℝ) (i j : Fin N) (h : ℝ) : Fin N → ℝ :=
  fun v => θ v+(if v=i then h else 0)-(if v=j then h else 0)

theorem extremeAnglePath_sum {N : ℕ} (θ : Fin N → ℝ) (i j : Fin N) (h : ℝ) :
    ∑ v, extremeAnglePath θ i j h v = ∑ v, θ v := by
  simp [extremeAnglePath, Finset.sum_sub_distrib, Finset.sum_add_distrib]

/-- The literal outstanding G1 obligation. All occupancies are computed
from the actual angle configuration through `deformedAngles`; the derivative
is the true real derivative of its constrained extreme path. Constants are
chosen before N, ε and the angles. This is a proposition definition, not an
axiom, a proved theorem, or an assumption used to claim a complete tail. -/
def PreferredExtremeCoareaStatement (d : PreferredBranchData)
    (B : PreferredCoareaBump d) : Prop :=
  ∃ C τ0 ε0 δB : ℝ, 0 < C ∧ 0 < τ0 ∧ 0 < ε0 ∧ 0 < δB ∧ δB < B.delta ∧
    ∀ τ : ℝ, 0 < τ → τ < τ0 → ∀ N : ℕ, 2 ≤ N → ∀ ε : ℝ,
      0 < ε → ε < ε0 → ∀ θ : Fin N → ℝ,
      (∀ v, θ v ∈ Icc (-d.b-δB) B.delta) →
      (∃ l : ℤ, (∑ v, θ v) = 2*Real.pi*(l:ℝ)) → ∀ i j : Fin N,
      (∀ v, θ i ≤ θ v ∧ θ v ≤ θ j) → 0 ≤ θ i+d.b → θ i < θ j →
      let D := (Complex.exp (-Complex.I*((3*Real.pi/8:ℝ):ℂ))*
        deriv (fun h : ℝ => preferredTotalPhase d ε τ B.p B.m (extremeAnglePath θ i j h)) 0).re
      0 < D ∧
        ‖(deriv (preferredAngularPhase d ε) (deformedAngles τ B.p B.m θ i)+1)*
          (deriv (preferredAngularPhase d ε) (deformedAngles τ B.p B.m θ j)+1)‖/D ≤
          C*Real.sqrt (θ j+d.b+ε)/(θ j-θ i)


/-- The actual one-dimensional change of variable behind q25. The two
extreme Jacobian factors remain inside F until the proved pair-over-projection
bound is used. This theorem isolates the change of variable; it does not assume
or establish such a bound for a physical configuration. -/
theorem projected_kernel_coarea_integral {c a x y K : ℝ} {v v' F : ℝ → ℝ}
    (hc : 0 < c) (ha : 0 < a) (ha1 : a ≤ 1) (hxy : x ≤ y) (hK : 0 ≤ K)
    (hv : ∀ t ∈ uIcc x y, HasDerivAt v (v' t) t)
    (hv' : ContinuousOn v' (uIcc x y))
    (hvpos : ∀ t ∈ uIcc x y, 0 ≤ v' t)
    (hF : ContinuousOn F (uIcc x y))
    (hpair : ∀ t ∈ uIcc x y, F t ≤ K*v' t) :
    (∫ t : ℝ in x..y, F t/(a+projectedDistance c (v t))) ≤
      K*(((c+1/(2*Real.pi))*max 1 c⁻¹*IsingBulk.Tail.simpleKernelConstant)*
        (1+(v y-v x))*(1+|Real.log a|)) := by
  let g := fun z : ℝ => (a+projectedDistance c z)⁻¹
  have hg : Continuous g := projected_reciprocal_continuous ha
  have hvc : ContinuousOn v (uIcc x y) := fun t ht =>
    (hv t ht).continuousAt.continuousWithinAt
  have hcomp : ContinuousOn (fun t => g (v t)) (uIcc x y) := hg.comp_continuousOn hvc
  have hsub := intervalIntegral.integral_comp_mul_deriv hv hv' hg
  have hmono : MonotoneOn v (Icc x y) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc x y)
    · simpa only [uIcc_of_le hxy] using hvc
    · intro t ht
      exact (hv t (by rw [uIcc_of_le hxy]; exact interior_subset ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      have htu : t ∈ uIcc x y := by rw [uIcc_of_le hxy]; exact interior_subset ht
      rw [(hv t htu).deriv]
      exact hvpos t htu
  have hends : v x ≤ v y := hmono (left_mem_Icc.mpr hxy) (right_mem_Icc.mpr hxy) hxy
  have hdom : (∫ t : ℝ in x..y, F t*g (v t)) ≤
      ∫ t : ℝ in x..y, K*(g (v t)*v' t) := by
    apply intervalIntegral.integral_mono_on hxy
      ((hF.mul hcomp).intervalIntegrable)
      ((continuousOn_const.mul (hcomp.mul hv')).intervalIntegrable)
    intro t ht
    have htu : t ∈ uIcc x y := by rwa [uIcc_of_le hxy]
    have hgp : 0 ≤ g (v t) := inv_nonneg.mpr
      (add_nonneg ha.le (projectedDistance_nonneg _ _))
    have h := mul_le_mul_of_nonneg_right (hpair t htu) hgp
    change F t*g (v t) ≤ K*(g (v t)*v' t)
    calc
      _ ≤ K*v' t*g (v t) := h
      _ = _ := by ring
  have hlog := projected_kernel_logarithmic_integral hc ha ha1 hends
  calc
    (∫ t : ℝ in x..y, F t/(a+projectedDistance c (v t))) =
        ∫ t : ℝ in x..y, F t*g (v t) := by simp only [g, div_eq_mul_inv]
    _ ≤ ∫ t : ℝ in x..y, K*(g (v t)*v' t) := hdom
    _ = K*(∫ z : ℝ in v x..v y, g z) := by
      rw [intervalIntegral.integral_const_mul]
      exact congrArg (fun z : ℝ => K*z) hsub
    _ ≤ _ := mul_le_mul_of_nonneg_left hlog hK


/-- The physical upper-dispersion chart never has zero phase sine. -/
theorem preferredArccos_sine_ne_zero_of_upper {W : ℂ} (hW : 0 < W.im) :
    Complex.sin (preferredArccos W) ≠ 0 := by
  intro hz
  have hs := Complex.sin_sq_add_cos_sq (preferredArccos W)
  rw [hz, zero_pow (by norm_num : (2:ℕ) ≠ 0), zero_add, cos_preferredArccos] at hs
  rcases sq_eq_one_iff.mp hs with h | h
  · rw [h] at hW
    norm_num at hW
  · rw [h] at hW
    norm_num at hW

/-- The exact derivative of the explicit physical slope on the full upper
W-half-plane. This identifies the compact-remainder quotient with −b_s'. -/
theorem preferredPhaseSlope_hasDerivAt {S w : ℂ}
    (hW : 0 < (S-Complex.cos w).im) :
    HasDerivAt (preferredPhaseSlope S) (-preferredPhaseCurvature S w) w := by
  let φ := fun z : ℂ => preferredArccos (S-Complex.cos z)
  have hi : AnalyticAt ℂ (fun z : ℂ => S-Complex.cos z) w := by fun_prop
  have ho : AnalyticAt ℂ preferredArccos (S-Complex.cos w) :=
    IsingBulk.Branch.lowerArccos_analytic_of_upper hW
  have hφ : AnalyticAt ℂ φ w :=
    AnalyticAt.comp (f := fun z : ℂ => S-Complex.cos z) (g := preferredArccos) ho hi
  have hs : Complex.sin (φ w) ≠ 0 := preferredArccos_sine_ne_zero_of_upper hW
  have hder : deriv φ w = preferredPhaseSlope S w := by
    apply phase_deriv_of_local_dispersion hφ.differentiableAt
    · exact Filter.Eventually.of_forall (fun z => cos_preferredArccos _)
    · exact hs
  have hd := ((Complex.hasDerivAt_sin w).neg).div
    ((Complex.hasDerivAt_sin (φ w)).comp w hφ.differentiableAt.hasDerivAt) hs
  rw [hder] at hd
  have hreduce := phase_curvature_quotient S (Complex.cos w) (Complex.sin w)
    (Complex.cos (φ w)) (Complex.sin (φ w)) hs (cos_preferredArccos _)
    (Complex.sin_sq_add_cos_sq w) (Complex.sin_sq_add_cos_sq (φ w))
  have he : ((-Complex.cos w)*Complex.sin (φ w)-(-Complex.sin w)*
      (Complex.cos (φ w)*preferredPhaseSlope S w))/(Complex.sin (φ w))^2 =
      -preferredPhaseCurvature S w := by
    calc
      _ = -S*(1-S*Complex.cos w+(Complex.cos w)^2)/(Complex.sin (φ w))^3 := hreduce
      _ = _ := by dsimp [preferredPhaseCurvature,φ]; ring
  simp only [Function.comp_apply, Pi.neg_apply] at hd
  rw [he] at hd
  convert! hd using 1

/-- Fixed-occupancy derivative of the actual bump angle. -/
theorem preferredBumpAngle_hasDerivAt {m p m' p' : ℝ → ℝ} {τ σ υ θ : ℝ}
    (hm : HasDerivAt m (m' θ) θ) (hp : HasDerivAt p (p' θ) θ) :
    HasDerivAt (preferredBumpAngle m p τ σ υ)
      (preferredBumpTangent m' p' τ σ υ θ) θ := by
  have hs := ((hm.const_mul σ).sub (hp.const_mul υ)).ofReal_comp
  have h := (hasDerivAt_id θ).ofReal_comp.sub (hs.const_mul (Complex.I*(τ:ℂ)))
  convert! h using 1

theorem preferredBumpTangent_hasDerivAt {m' p' m'' p'' : ℝ → ℝ} {τ σ υ θ : ℝ}
    (hm : HasDerivAt m' (m'' θ) θ) (hp : HasDerivAt p' (p'' θ) θ) :
    HasDerivAt (preferredBumpTangent m' p' τ σ υ)
      (preferredBumpSecond m'' p'' τ σ υ θ) θ := by
  have hs := ((hm.const_mul σ).sub (hp.const_mul υ)).ofReal_comp
  have h := (hs.const_mul (Complex.I*(τ:ℂ))).const_sub 1
  convert! h using 1
  simp [preferredBumpSecond]

/-- True differentiation of B=b_s(f) f' on the compact right remainder.
Both bump second derivatives are retained, and the physical upper W-domain
is explicit. Combined with the derived compact estimate this supplies G4 there. -/
theorem preferredCompactTransport_hasDerivAt (d : PreferredBranchData)
    {m p m' p' m'' p'' : ℝ → ℝ} {ε τ σ υ θ : ℝ}
    (hm : HasDerivAt m (m' θ) θ) (hp : HasDerivAt p (p' θ) θ)
    (hm' : HasDerivAt m' (m'' θ) θ) (hp' : HasDerivAt p' (p'' θ) θ)
    (hW : 0 < (preferredRadialTrace d ε-Complex.cos (preferredBumpAngle m p τ σ υ θ)).im) :
    HasDerivAt
      (fun v => preferredCompactSlope d m p ε τ σ υ v*preferredBumpTangent m' p' τ σ υ v)
      (-preferredCompactTransportCurvature d m p m' p' m'' p'' ε τ σ υ θ) θ := by
  have hf := preferredBumpAngle_hasDerivAt (τ := τ) (σ := σ) (υ := υ) hm hp
  have ha := preferredBumpTangent_hasDerivAt (τ := τ) (σ := σ) (υ := υ) hm' hp'
  have hb : HasDerivAt (preferredCompactSlope d m p ε τ σ υ)
      (-preferredCompactCurvature d m p ε τ σ υ θ*preferredBumpTangent m' p' τ σ υ θ) θ := by
    have h := (preferredPhaseSlope_hasDerivAt hW).scomp θ hf
    simp only [Function.comp_def, smul_eq_mul] at h
    convert! h using 1
    unfold preferredCompactCurvature
    ring
  have h := hb.mul ha
  convert! h using 1
  dsimp [preferredCompactTransportCurvature]
  ring


/-- The actual contour velocity is linear in the real angular motion. -/
theorem balancedContourVelocity_sub {ι : Type*} [Fintype ι]
    (κ : ℝ) (p m : ℝ → ℝ) (θ v₁ v₂ dp dm : ι → ℝ) (i : ι) :
    balancedContourVelocity κ p m θ (fun j => v₁ j-v₂ j) dp dm i =
      balancedContourVelocity κ p m θ v₁ dp dm i-
        balancedContourVelocity κ p m θ v₂ dp dm i := by
  unfold balancedContourVelocity
  simp only [mul_sub, Finset.sum_sub_distrib]
  push_cast
  ring

/-- G5 along the literal constrained extreme path, with the real occupancy
functions differentiated by the chain rule and both occupancy corrections retained. -/
theorem hasDerivAt_totalPhase_extreme {N : ℕ} (τ : ℝ)
    {p m : ℝ → ℝ} {θ dp dm : Fin N → ℝ} {φ : ℂ → ℂ} {b : Fin N → ℂ}
    (i j : Fin N)
    (hp : ∀ v, HasDerivAt p (dp v) (θ v))
    (hm : ∀ v, HasDerivAt m (dm v) (θ v))
    (hφ : ∀ v, HasDerivAt φ (b v) (deformedAngles τ p m θ v)) :
    HasDerivAt (fun h : ℝ => ∑ v, φ (deformedAngles τ p m (extremeAnglePath θ i j h) v))
      ((∑ v, b v*occupancyJacobianColumn (Complex.I*((τ/(N:ℝ):ℝ):ℂ))
        (fun v => (p (θ v):ℂ)) (fun v => (m (θ v):ℂ))
        (fun v => (dp v:ℂ)) (fun v => (dm v:ℂ)) i v)-
       (∑ v, b v*occupancyJacobianColumn (Complex.I*((τ/(N:ℝ):ℝ):ℂ))
        (fun v => (p (θ v):ℂ)) (fun v => (m (θ v):ℂ))
        (fun v => (dp v:ℂ)) (fun v => (dm v:ℂ)) j v)) 0 := by
  have hz : extremeAnglePath θ i j 0 = θ := by ext v; simp [extremeAnglePath]
  have hd (v : Fin N) : HasDerivAt (fun h : ℝ => extremeAnglePath θ i j h v)
      ((if v=i then 1 else 0)-(if v=j then 1 else 0)) 0 := by
    have hi : HasDerivAt (fun h : ℝ => if v=i then h else 0) (if v=i then 1 else 0) 0 := by
      split_ifs
      · exact hasDerivAt_id 0
      · exact hasDerivAt_const 0 0
    have hj : HasDerivAt (fun h : ℝ => if v=j then h else 0) (if v=j then 1 else 0) 0 := by
      split_ifs
      · exact hasDerivAt_id 0
      · exact hasDerivAt_const 0 0
    simpa only [extremeAnglePath, Pi.add_def, Pi.sub_def, zero_add] using
      ((hasDerivAt_const 0 (θ v)).add hi).sub hj
  have h := hasDerivAt_balancedPhase (κ := τ/N) hd
    (by simpa only [hz] using hp) (by simpa only [hz] using hm)
    (by simpa only [hz, balancedContourPoint_eq_deformedAngles] using hφ)
  simp_rw [hz, balancedContourVelocity_sub, balancedContourVelocity_column,
    mul_sub, Finset.sum_sub_distrib] at h
  simpa only [balancedContourPoint_eq_deformedAngles] using h


/-- The actual complex angular phase derivative on its full physical
upper-dispersion domain, used in the complete constrained G5 chain rule. -/
theorem preferredAngularPhase_hasDerivAt (d : PreferredBranchData) (ε : ℝ) {w : ℂ}
    (hW : 0 < (preferredRadialTrace d ε-Complex.cos w).im) :
    HasDerivAt (preferredAngularPhase d ε) (preferredPhaseSlope (preferredRadialTrace d ε) w) w := by
  have hi : AnalyticAt ℂ (fun z : ℂ => preferredRadialTrace d ε-Complex.cos z) w := by fun_prop
  have ho : AnalyticAt ℂ preferredArccos (preferredRadialTrace d ε-Complex.cos w) :=
    IsingBulk.Branch.lowerArccos_analytic_of_upper hW
  have hφ : AnalyticAt ℂ (preferredAngularPhase d ε) w :=
    AnalyticAt.comp (f := fun z : ℂ => preferredRadialTrace d ε-Complex.cos z)
      (g := preferredArccos) ho hi
  have hs : Complex.sin (preferredAngularPhase d ε w) ≠ 0 :=
    preferredArccos_sine_ne_zero_of_upper hW
  have hder : deriv (preferredAngularPhase d ε) w =
      preferredPhaseSlope (preferredRadialTrace d ε) w := by
    apply phase_deriv_of_local_dispersion hφ.differentiableAt
    · exact Filter.Eventually.of_forall (fun z => cos_preferredArccos _)
    · exact hs
  have h := hφ.differentiableAt.hasDerivAt
  rw [hder] at h
  exact h

end
end IsingBulk.Preferred22
