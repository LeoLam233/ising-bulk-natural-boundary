import IsingBulk.First.MeanResidueDomain
import IsingBulk.First.MeanConstrainedConcavity
import IsingBulk.First.MeanRadialTaylor

/-! Actual post-residue real-phase separation on zero-sum shape tuples. -/
namespace IsingBulk.First
noncomputable section
open Set
open scoped BigOperators

theorem radialResiduePhase_concavity_sum (a : OrderedChartData) :
    ∃ r : ℝ, 0 < r ∧ ∀ (N : ℕ), 0 < N → ∀ (epsilon : ℝ) (t : Fin N → ℝ),
      0 < epsilon → epsilon < r → (∀ i, |t i| < r) → (∑ i, t i = 0) →
      (∑ i, (radialResiduePhase a (epsilon:ℂ) (t i:ℂ)).re) ≤
        N*(radialResiduePhase a (epsilon:ℂ) 0).re - (a.d/2)*∑ i, (t i)^2 := by
  obtain ⟨rD,hrD,hD⟩ := radialResidueW_domain a (by norm_num : (0:ℝ)<1)
  obtain ⟨rS,hrS,hS⟩ := radialResidueSecond_negative a
  let r := min rD rS
  refine ⟨r,lt_min hrD hrS,?_⟩
  intro N hN epsilon t he her ht hsum
  let T := complexRadialTrace a.theta (epsilon:ℂ)
  let g := realRegularMeanPhase T a.alpha
  have hquad (u : ℝ) (hu : u ∈ Ioo (-r) r) :
      0 < (T-Complex.cos ((u:ℂ)-(a.alpha:ℂ))).re ∧
        0 < (T-Complex.cos ((u:ℂ)-(a.alpha:ℂ))).im := by
    have hd := hD epsilon u he (her.trans_le (min_le_left _ _))
      ((abs_lt.mpr hu).trans_le (min_le_left _ _))
    exact ⟨hd.1, hd.2.1⟩
  have hfirst (u : ℝ) (hu : u ∈ Ioo (-r) r) : HasDerivAt g (deriv g u) u :=
    (realRegularMeanPhase_hasDerivAt T a.alpha u (hquad u hu).1 (hquad u hu).2).differentiableAt.hasDerivAt
  have hsecond (u : ℝ) (hu : u ∈ Ioo (-r) r) :
      HasDerivAt (deriv g) (radialResidueSecond a (epsilon,u)).re u :=
    realRegularMeanPhase_second_hasDerivAt T a.alpha u (hquad u hu).1 (hquad u hu).2
  have hbound (u : ℝ) (hu : u ∈ Ioo (-r) r) : (radialResidueSecond a (epsilon,u)).re ≤ -a.d :=
    hS epsilon u (by rw [abs_of_pos he]; exact her.trans_le (min_le_right _ _))
      ((abs_lt.mpr hu).trans_le (min_le_right _ _))
  exact constrained_concavity_sum hN g (deriv g) (fun u => (radialResidueSecond a (epsilon,u)).re)
    hfirst hsecond hbound t (fun i => abs_lt.mp (ht i)) hsum

/-- Center Taylor error and true concavity combine into the actual shape
phase separation; the coefficient is uniform before epsilon and t vary. -/
theorem radialResiduePhase_sum_separation (a : OrderedChartData) :
    ∃ C r : ℝ, 0 < C ∧ 0 < r ∧ ∀ (N : ℕ), 0 < N → ∀ (epsilon : ℝ) (t : Fin N → ℝ),
      0 < epsilon → epsilon < r → (∀ i, |t i| < r) → (∑ i, t i = 0) →
      (a.d/2)*∑ i, (t i)^2 - N*C*epsilon^2 ≤
        N*a.beta-∑ i, (radialResiduePhase a (epsilon:ℂ) (t i:ℂ)).re := by
  obtain ⟨C,rT,hC,hrT,hT⟩ := radial_center_phase_error a 0
  obtain ⟨rS,hrS,hS⟩ := radialResiduePhase_concavity_sum a
  refine ⟨C,min rT rS,hC,lt_min hrT hrS,?_⟩
  intro N hN epsilon t he her ht hsum
  have hconc := hS N hN epsilon t he (her.trans_le (min_le_right _ _))
    (fun i => (ht i).trans_le (min_le_right _ _)) hsum
  have hcenter := hT epsilon (by rw [abs_of_pos he]; exact her.trans_le (min_le_left _ _))
  rw [← radialResiduePhase_eq_radialRegularPhase] at hcenter
  have hupper := (abs_le.mp hcenter).2
  have hNreal : (0:ℝ) ≤ N := Nat.cast_nonneg _
  have hm := mul_le_mul_of_nonneg_left hupper hNreal
  nlinarith

end
end IsingBulk.First
