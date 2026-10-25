import IsingBulk.Joint.FormFactors.Conjugation
import IsingBulk.Joint.RegularEdges.PhysicalAngular

/-! Particlewise Schwarz reflection for the literal joint full contour
coefficients. The real coefficient identity is imported exactly from the
baseline; no real spin-family or bulk reflection premise is used. -/
namespace IsingBulk.Joint.FormFactors
noncomputable section
open Set Filter Metric
open scoped Topology

theorem multiAngleIntegral_star (N : ℕ) (f : (Fin N→ℝ)→ℂ) :
    star (IsingBulk.First.multiAngleIntegral N f)=
      IsingBulk.First.multiAngleIntegral N (fun q=>star (f q)) := by
  induction N with
  | zero => rfl
  | succ n ih =>
    simp only [IsingBulk.First.multiAngleIntegral,ih]
    congr 1
    funext q
    exact intervalIntegral.intervalIntegral_conj.symm

theorem realAngularCoefficient_star (n : ℕ) (B C : ℝ) :
    star (Anisotropic.FormFactors.angularCoefficient n B C)=
      Anisotropic.FormFactors.angularCoefficient n B C := by
  simp [Anisotropic.FormFactors.angularCoefficient,multiAngleIntegral_star]

/-- The actual full coefficient is real on every independent positive real
physical pair away from criticality. -/
theorem unscaledFullCoefficient_real_star (N : ℕ) (hN : 0<N) {x y : ℝ}
    (hx : 0<x) (hy : 0<y) (hp : Real.sinh x*Real.sinh y≠1)
    (hK : ((x:ℂ),(y:ℂ))∉spectralSet) :
    star (unscaledFullCoefficient N ((x:ℂ),(y:ℂ)))=
      unscaledFullCoefficient N ((x:ℂ),(y:ℂ)) := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hN)
  let lam := y/x
  have hl : 0<lam := div_pos hy hx
  have he : ratioSlice lam (x:ℂ)=((x:ℂ),(y:ℂ)) := by
    apply Prod.ext
    · rfl
    · change ((y/x:ℝ):ℂ)*(x:ℂ)=(y:ℂ)
      exact_mod_cast div_mul_cancel₀ y hx.ne'
  have hp' : Anisotropic.FormFactors.realProduct lam x≠1 := by
    simpa [Anisotropic.FormFactors.realProduct,lam,div_mul_cancel₀ y hx.ne'] using hp
  have hs : (x:ℂ)∉Anisotropic.spectralSet lam := by
    change ratioSlice lam (x:ℂ)∉spectralSet
    rwa [he]
  rw [←he,unscaledFullCoefficient_ratioSlice (n+1) (by omega) hs]
  have hprod : 0<Anisotropic.FormFactors.realProduct lam x :=
    mul_pos (Real.sinh_pos_iff.mpr hx) (Real.sinh_pos_iff.mpr (mul_pos hl hx))
  have hc := Anisotropic.RegularEdges.scaled_unscaledFullCoefficient_eq_angular n hl hx hp'
  have hcstar := congrArg star hc
  rw [realAngularCoefficient_star] at hcstar
  have hfac : (((Real.sqrt (Anisotropic.FormFactors.realProduct lam x))^(n+1):ℝ):ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (pow_ne_zero _ (Real.sqrt_pos.mpr hprod).ne')
  apply mul_left_cancel₀ hfac
  simp only [star_mul,Complex.star_def,Complex.conj_ofReal] at hcstar
  simpa only [Complex.star_def,mul_comm] using hcstar.trans hc.symm

/-- Particlewise reflection on the entire high-temperature component,
including its removable axes. -/
theorem unscaledFullCoefficient_conjugate_high (N : ℕ) (hN : 0<N)
    {K : Coupling} (hK : K∈highDomain) :
    unscaledFullCoefficient N (star K)=star (unscaledFullCoefficient N K) := by
  let x := Anisotropic.criticalPoint 1/2
  have hc : 0<Anisotropic.criticalPoint 1 := Anisotropic.criticalPoint_pos (by norm_num)
  have hx : 0<x := by dsimp [x]; positivity
  have hxc : x<Anisotropic.criticalPoint 1 := by dsimp [x]; linarith
  have hxy : ((x:ℂ),(x:ℂ))∈highDomain := by
    have hh : (x:ℂ)∈ratioSlice 1 ⁻¹' highDomain := by
      rw [highDomain_pullback (by norm_num)]
      exact Anisotropic.real_mem_omegaH_of_nonneg_lt_critical (by norm_num) hx.le hxc
    simpa [ratioSlice] using hh
  have hh := reflection_eqOn_of_real_physical_point highDomain_isOpen highDomain_isPreconnected
    star_mem_highDomain_iff
    ((unscaledFullCoefficient_differentiableOn N hN).mono highDomain_subset_spectralComplement)
    (fun a c ha hc hL=>unscaledFullCoefficient_real_star N hN ha hc
      ((realPositive_mem_high_iff ha hc).mp hL).ne (highDomain_subset_spectralComplement hL)) hx hx hxy
  simpa only [star_star] using congrArg star (hh hK)

/-- Particlewise reflection on the actual low-temperature component. -/
theorem unscaledFullCoefficient_conjugate_low (N : ℕ) (hN : 0<N)
    {K : Coupling} (hK : K∈lowDomain) :
    unscaledFullCoefficient N (star K)=star (unscaledFullCoefficient N K) := by
  let x := Anisotropic.criticalPoint 1+1
  have hc : 0<Anisotropic.criticalPoint 1 := Anisotropic.criticalPoint_pos (by norm_num)
  have hx : 0<x := by dsimp [x]; linarith
  have hxc : Anisotropic.criticalPoint 1<x := by dsimp [x]; linarith
  have hxy : ((x:ℂ),(x:ℂ))∈lowDomain := by
    have hh : (x:ℂ)∈ratioSlice 1 ⁻¹' lowDomain := by
      rw [lowDomain_pullback (by norm_num)]
      exact (Anisotropic.real_mem_omegaL_iff (by norm_num) x).mpr hxc
    simpa [ratioSlice] using hh
  have hh := reflection_eqOn_of_real_physical_point lowDomain_isOpen lowDomain_isPreconnected
    star_mem_lowDomain_iff
    ((unscaledFullCoefficient_differentiableOn N hN).mono lowDomain_subset_spectralComplement)
    (fun a c ha hc hL=>unscaledFullCoefficient_real_star N hN ha hc
      ((realPositive_mem_low_iff ha hc).mp hL).ne' (lowDomain_subset_spectralComplement hL)) hx hx hxy
  simpa only [star_star] using congrArg star (hh hK)

@[simp] theorem p_star (K : Coupling) : p (star K)=star (p K) := by
  simp [p,S,T,Complex.sinh_conj]

/-- The same principal fourth-root branch commutes with conjugation on its
proved slit-plane domain. -/
theorem fourthRoot_star {v : ℂ} (hv : v∈Complex.slitPlane) :
    fourthRoot (star v)=star (fourthRoot v) := by
  unfold fourthRoot
  simp only [Complex.star_def]
  rw [Complex.log_conj _ (Complex.slitPlane_arg_ne_pi hv),←Complex.exp_conj]
  congr 1
  simp only [map_mul,map_div₀,map_one,map_ofNat]

theorem highPrefactor_conjugate {K : Coupling} (hK : K∈highDomain) :
    highPrefactor (star K)=star (highPrefactor K) := by
  simpa only [highPrefactor,p_star,star_sub,star_one,star_pow] using
    fourthRoot_star (one_sub_sq_mem_slitPlane (norm_p_lt_one hK))

theorem lowPrefactor_conjugate {K : Coupling} (hK : K∈lowDomain) :
    lowPrefactor (star K)=star (lowPrefactor K) := by
  have hp := one_lt_norm_p hK
  have hpi : ‖(p K)⁻¹‖<1 := by rw [norm_inv]; exact (inv_lt_one₀ (zero_lt_one.trans hp)).mpr hp
  simpa [lowPrefactor,p_star] using fourthRoot_star (one_sub_sq_mem_slitPlane hpi)

end
end IsingBulk.Joint.FormFactors
