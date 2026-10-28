import IsingBulk.HT22.First.LocalLimit.FixedCutoff
import IsingBulk.HT22.Arithmetic.FullFamily

namespace IsingBulk.HT22.LocalLimit
noncomputable section
open Complex Set Filter Metric IsingBulk.First IsingBulk.HT.First IsingBulk.Branch
open IsingBulk.PrimeFamily Arithmetic
open scoped Topology ContDiff

theorem prime_equal_angle_resonance {p : ℕ} (hp : p≠0) (a : ℤ) :
    exp (-(p:ℂ)*(angle p a:ℂ)*I)=1 := by
  rw [show -(p:ℂ)*(angle p a:ℂ)*I = -((p:ℂ)*((angle p a:ℂ)*I)) by ring,
    exp_neg,exp_nat_mul]
  change (angleRoot p a^p)⁻¹=1
  rw [angleRoot_pow hp,inv_one]

/-- Every member of the exact prime family admits the actual two-chart
asymptotic, without any additional resonance or sign hypothesis. -/
theorem prime_two_chart_asymptotic {p : ℕ} (hp : p.Prime) (hp5 : 5≤p)
    {a : ℤ} (ha : PrimeIndex p a) :
    equalAngleLeadingCoefficient p (angle p a)≠0 ∧
    ∃ χ : ShapeSpace (p-1) → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      (∀ x,0≤χ x ∧ χ x≤1) ∧ χ =ᶠ[𝓝 0] (fun _ => 1) ∧
      Asymptotics.IsLittleO (𝓝[>] (0:ℝ))
        (fun ε => (deriv^[derivativeOrder p]
          (angularTwoChartIntegral (angle p a) (fun x => (χ x:ℂ))))
          (radialParameter (angle p a) ε)-(ε:ℂ)⁻¹*equalAngleLeadingCoefficient p (angle p a))
        (fun ε => (ε:ℂ)⁻¹) := by
  have ho : Odd p := hp.odd_of_ne_two (by omega)
  obtain ⟨hα,hαπ⟩ := primeIndex_angle_bounds hp.pos ha
  have hc : Real.cos (angle p a)≠0 := by
    intro hz
    exact primeRoot_level_ne_zero hp hp5 ha (by rw [hz,mul_zero])
  have he : p-1+1=p := by omega
  refine ⟨equalAngleLeadingCoefficient_radial_nonzero ho (by omega) hα hαπ hc,?_⟩
  have hep : ((p-1:ℕ):ℂ)+1=(p:ℂ) := by exact_mod_cast he
  have hres := prime_equal_angle_resonance hp.ne_zero a
  have ht := exists_equalAngle_two_chart_asymptotic (n:=p-1) (by omega)
    (he.symm ▸ ho) (angle p a) hα hαπ hc (by rw [hep];exact hres)
  simpa only [he] using ht

end
end IsingBulk.HT22.LocalLimit
