import IsingBulk.Anisotropic.NegativeCycles.ActualHomotopyPole

noncomputable section
namespace IsingBulk.Anisotropic.NegativeCycles
open IsingBulk.Anisotropic.NegativeNormalForm Set
open scoped BigOperators

theorem actual_real_pole_uniform_positive (B : ℂ→ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) (hB : AnalyticAt ℂ B 0) (hBn : B 0≠0)
    (r C R : ℝ) (hr : 0<r) (hR : 0<R) (hRr : R≤r/2) :
    ∃ρ : ℝ,0<ρ ∧ ∀n : ℕ,n≠0 → ∀d : ℝ,|d|<ρ → d≠0 →
      ∀P : UniformProjectedWitness B phi hphi n (d:ℂ) r C,
      ∀_J : UniformCorrectionWitness B phi hphi n (d:ℂ) r C P R,
      ∀v : Fin n→ℝ, ‖fun i => (v i:ℂ)‖≤ρ → (∑i,v i)=0 →
      0<1-Real.cos d ∧ 1-Real.cos d≤(P.T (fun i => (v i:ℂ))).re := by
  obtain ⟨a,ha,_har,hsec⟩ := actualHomotopy_pole_uniform_sector B phi hphi hB hBn r C R hr hR hRr
  let ρ := min a (Real.pi/2)
  have hρ : 0<ρ := lt_min ha (by positivity)
  have hρa : ρ≤a := min_le_left _ _
  have hρpi : ρ≤Real.pi/2 := min_le_right _ _
  refine ⟨ρ,hρ,?_⟩
  intro n hn d hd hd0 P J v hv hm
  have htau : 0<1-Real.cos d := by
    have hh := Real.cos_lt_cos_of_nonneg_of_le_pi (show (0:ℝ)≤0 by norm_num)
      (show |d|≤Real.pi by linarith) (abs_pos.mpr hd0)
    simpa only [Real.cos_abs,Real.cos_zero,sub_pos] using hh
  have hh := hsec n hn d (by simpa using hd.trans_le hρa) P J v (hv.trans hρa) hm 0
    (by constructor <;> norm_num)
  simp only [correctedHomotopy,Complex.ofReal_zero,zero_smul,add_zero] at hh
  refine ⟨htau,?_⟩
  have hnon : 0≤(∑i,v i^2)/(8*n) := by positivity
  linarith

end IsingBulk.Anisotropic.NegativeCycles
