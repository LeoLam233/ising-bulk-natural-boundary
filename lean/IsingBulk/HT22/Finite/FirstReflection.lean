import IsingBulk.HT22.First.LocalLimit.SignedPrimeCharts
namespace IsingBulk.HT22.Finite
noncomputable section
open Complex Set Filter IsingBulk.First IsingBulk.Branch IsingBulk.HT.First
open IsingBulk.PrimeFamily Arithmetic LocalLimit Physical
open scoped Topology
set_option backward.isDefEq.respectTransparency false

theorem positiveCoefficient_iteratedDeriv_reflected {n : ℕ} (ho : Odd (n+1))
    (j : ℕ) {s : ℂ} (hs : 1<‖s‖) :
    iteratedDeriv j (signedCoefficient false (n+1)) s=
      -((-1:ℂ)^j*star (iteratedDeriv j (signedCoefficient true (n+1)) (-star s))) := by
  have he : signedCoefficient false (n+1) =ᶠ[𝓝 s]
      (fun z => -star (signedCoefficient true (n+1) (-star z))) := by
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hs] with z hz
    have hh := signedCoefficient_odd_neg ho (t := -star z) (by simpa using hz)
    rw [neg_neg,signedCoefficient_conj false (n+1) hz] at hh
    have hh' := congrArg star hh
    simpa only [star_star,star_neg] using hh'
  rw [he.iteratedDeriv_eq j,iteratedDeriv_fun_neg,
    IsingBulk.HT.Contour.iteratedDeriv_star_neg_conj]

theorem original_first_limit_of_effective_signed {p : ℕ} (hp : p.Prime) (hp5 : 5≤p)
    {a : ℤ} (ha : PrimeIndex p a)
    (hlim : Tendsto (fun ε : ℝ => ε • iteratedDeriv (derivativeOrder p)
      (signedCoefficient (negativeSide (angle p a)) p)
      (radialParameter (primeBranchData hp hp5 ha).alpha ε))
      (𝓝[>] 0) (𝓝 (physicalCriticalLeadingCoefficient p (angle p a)))) :
    Tendsto (fun ε : ℝ => ε • iteratedDeriv (derivativeOrder p)
      (signedCoefficient false p) (radialParameter (angle p a) ε))
      (𝓝[>] 0) (𝓝 (equalAngleLeadingCoefficient p (angle p a))) := by
  by_cases hn : Real.pi/2<angle p a
  · have hlim' : Tendsto (fun ε : ℝ => ε • iteratedDeriv (derivativeOrder p)
        (signedCoefficient true p) (radialParameter (Real.pi-angle p a) ε))
        (𝓝[>] 0) (𝓝 (signedCriticalLeadingCoefficient p (angle p a))) := by
      simpa only [primeBranchData,positiveTraceBranchData,effectiveAngle,ite_eq_left hn,
        negativeSide,decide_eq_true hn,physicalCriticalLeadingCoefficient,↓reduceIte] using hlim
    have ht := ((continuous_star.tendsto _).comp hlim').const_mul (-((-1:ℂ)^derivativeOrder p))
    have he : p-1+1=p := by omega
    have ho : Odd (p-1+1) := he.symm ▸ hp.odd_of_ne_two (by omega)
    have hresult : Tendsto (fun ε : ℝ => ε • iteratedDeriv (derivativeOrder p)
        (signedCoefficient false p) (radialParameter (angle p a) ε))
        (𝓝[>] 0) (𝓝 (-((-1:ℂ)^derivativeOrder p)*star (signedCriticalLeadingCoefficient p (angle p a)))) := by
      apply ht.congr'
      filter_upwards [self_mem_nhdsWithin] with ε hε
      have hε : 0<ε := hε
      have hh := positiveCoefficient_iteratedDeriv_reflected ho (derivativeOrder p)
        (s := radialParameter (angle p a) ε) (by rw [radialParameter_norm hε.le];linarith)
      rw [he] at hh
      dsimp only [Function.comp_def]
      rw [hh,IsingBulk.HT.Contour.radialParameter_neg_conjugate]
      simp only [real_smul,star_mul',Complex.star_def,Complex.conj_ofReal]
      ring
    simpa only [neg_mul,signedCriticalLeadingCoefficient_transfer_back] using hresult
  · simpa only [primeBranchData,positiveTraceBranchData,effectiveAngle,ite_eq_right hn,
      negativeSide,decide_eq_false hn,physicalCriticalLeadingCoefficient,Bool.false_eq_true,↓reduceIte] using hlim

end
end IsingBulk.HT22.Finite
