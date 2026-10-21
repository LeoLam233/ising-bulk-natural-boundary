import IsingBulk.First.RegularResidueDomain
import IsingBulk.First.RegularRadialTaylor
import IsingBulk.First.MeanConstrainedConcavity

/-! Sign-independent regular phase foundation for the actual source. -/
namespace IsingBulk.First.Regular
noncomputable section
open Complex Filter Set IsingBulk.Branch
open scoped Topology BigOperators

theorem radialResiduePhase_concavity_sum (a : RegularChartData) :
    ∃ r : ℝ, 0 < r ∧ ∀ (N : ℕ), 0 < N → ∀ (epsilon : ℝ) (t : Fin N → ℝ),
      0 < epsilon → epsilon < r → (∀ i, |t i| < r) → (∑ i, t i = 0) →
      a.curvatureSign*(∑ i, (radialResiduePhase a (epsilon:ℂ) (t i:ℂ)).re) ≤
        N*(a.curvatureSign*(radialResiduePhase a (epsilon:ℂ) 0).re) -
          (|a.d|/2)*∑ i, (t i)^2 := by
  obtain ⟨rD,hrD,hD⟩ := radialResidueW_domain a (by norm_num : (0:ℝ)<1)
  obtain ⟨rS,hrS,hS⟩ := radialResidueSecond_signed_negative a
  let r := min rD rS
  refine ⟨r,lt_min hrD hrS,?_⟩
  intro N hN epsilon t he her ht hsum
  let T := complexRadialTrace a.theta (epsilon:ℂ)
  let g := realRegularMeanPhase T a.alpha
  have hupper (u : ℝ) (hu : u ∈ Set.Ioo (-r) r) :
      0 < (T-Complex.cos ((u:ℂ)-(a.alpha:ℂ))).im := by
    exact (hD epsilon u he (her.trans_le (min_le_left _ _))
      ((abs_lt.mpr hu).trans_le (min_le_left _ _))).1
  have hfirst (u : ℝ) (hu : u ∈ Set.Ioo (-r) r) :
      HasDerivAt (fun v => a.curvatureSign*g v) (a.curvatureSign*deriv g u) u :=
    ((realRegularMeanPhase_hasDerivAt_upper T a.alpha u (hupper u hu)).differentiableAt.hasDerivAt).const_mul _
  have hsecond (u : ℝ) (hu : u ∈ Set.Ioo (-r) r) :
      HasDerivAt (fun v => a.curvatureSign*deriv g v)
        (a.curvatureSign*(radialResidueSecond a (epsilon,u)).re) u :=
    (realRegularMeanPhase_second_hasDerivAt_upper T a.alpha u (hupper u hu)).const_mul _
  have hbound (u : ℝ) (hu : u ∈ Set.Ioo (-r) r) :
      a.curvatureSign*(radialResidueSecond a (epsilon,u)).re ≤ -|a.d| :=
    hS epsilon u (by rw [abs_of_pos he]; exact her.trans_le (min_le_right _ _))
      ((abs_lt.mpr hu).trans_le (min_le_right _ _))
  have hh := constrained_concavity_sum hN
    (fun v => a.curvatureSign*g v) (fun v => a.curvatureSign*deriv g v)
    (fun u => a.curvatureSign*(radialResidueSecond a (epsilon,u)).re)
    hfirst hsecond hbound t (fun i => abs_lt.mp (ht i)) hsum
  simpa only [g,T,realRegularMeanPhase,radialResiduePhase,Complex.ofReal_zero,← Finset.mul_sum] using hh

/-- Signed phase separation on the actual radius-free zero-sum shape. -/
theorem radialResiduePhase_sum_separation (a : RegularChartData) :
    ∃ C r : ℝ, 0 < C ∧ 0 < r ∧ ∀ (N : ℕ), 0 < N → ∀ (epsilon : ℝ) (t : Fin N → ℝ),
      0 < epsilon → epsilon < r → (∀ i, |t i| < r) → (∑ i, t i = 0) →
      (|a.d|/2)*∑ i, (t i)^2 - N*C*epsilon^2 ≤
        a.curvatureSign*(N*a.beta-∑ i, (radialResiduePhase a (epsilon:ℂ) (t i:ℂ)).re) := by
  obtain ⟨C,rT,hC,hrT,hT⟩ := radial_center_phase_error a 0
  obtain ⟨rS,hrS,hS⟩ := radialResiduePhase_concavity_sum a
  refine ⟨C,min rT rS,hC,lt_min hrT hrS,?_⟩
  intro N hN epsilon t he her ht hsum
  have hconc := hS N hN epsilon t he (her.trans_le (min_le_right _ _))
    (fun i => (ht i).trans_le (min_le_right _ _)) hsum
  have hcenter := hT epsilon (by rw [abs_of_pos he]; exact her.trans_le (min_le_left _ _))
  rw [← radialResiduePhase_eq_radialRegularPhase] at hcenter
  have hupper : a.curvatureSign*((radialResiduePhase a (epsilon:ℂ) 0).re-a.beta) ≤ C*epsilon^2 := by
    rcases a.curvatureSign_cases with hs | hs
    · rw [hs, one_mul]
      exact (abs_le.mp hcenter).2
    · rw [hs, neg_one_mul]
      linarith [(abs_le.mp hcenter).1]
  have hm := mul_le_mul_of_nonneg_left hupper (Nat.cast_nonneg N : (0:ℝ)≤N)
  nlinarith

end
end IsingBulk.First.Regular
