import IsingBulk.HT22.PhysicalScope.ReflectionJets
import IsingBulk.HT22.First.LocalLimit.SignedCriticalCharts

/-! The signed positive-trace first limit restores the exact original F001
coefficient, including its phase, in the second upper quadrant. -/
namespace IsingBulk.HT22.Final
noncomputable section
open Physical PhysicalScope LocalLimit Filter IsingBulk.Branch
open scoped Topology

theorem original_first_limit_from_signed {p : ℕ} (hp : Odd p) (α : ℝ)
    (hfirst : Tendsto (fun ε : ℝ => ε •
      iteratedDeriv (IsingBulk.HT.First.derivativeOrder p) (signedCoefficient true p)
        (radialParameter (Real.pi-α) ε)) (𝓝[>] 0)
      (𝓝 (signedCriticalLeadingCoefficient p α))) :
    Tendsto (fun ε : ℝ => ε •
      iteratedDeriv (IsingBulk.HT.First.derivativeOrder p) (coefficient p)
        (radialParameter α ε)) (𝓝[>] 0) (𝓝 (equalAngleLeadingCoefficient p α)) := by
  obtain ⟨n,rfl⟩ := hp
  let j := IsingBulk.HT.First.derivativeOrder (2*n+1)
  have hh := ((continuous_star.tendsto _).comp hfirst).const_mul (-((-1:ℂ)^j))
  have hphase : -((-1:ℂ)^j)*star (signedCriticalLeadingCoefficient (2*n+1) α)=
      equalAngleLeadingCoefficient (2*n+1) α := by
    simpa only [j,neg_mul] using signedCriticalLeadingCoefficient_transfer_back (2*n+1) α
  rw [hphase] at hh
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε : 0<ε := hε
  have ht : 1<‖radialParameter α ε‖ := by
    rw [IsingBulk.First.radialParameter_norm hε.le]
    linarith
  simp only [Function.comp_def]
  rw [IsingBulk.HT.Contour.radialParameter_neg_conjugate]
  have hi := signed_negative_reflected_derivative_involution n j ht
  simp only [Complex.real_smul,star_mul',Complex.star_def,Complex.conj_ofReal]
  change _=ε*iteratedDeriv j (coefficient (2*n+1)) (radialParameter α ε)
  rw [←hi]
  simp only [j,Complex.star_def]
  ring

end
end IsingBulk.HT22.Final
