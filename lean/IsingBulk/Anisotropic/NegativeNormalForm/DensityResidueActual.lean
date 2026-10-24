import IsingBulk.Anisotropic.NegativeNormalForm.DensityResidueUniform
import IsingBulk.Anisotropic.NegativeNormalForm.UniformCorrectedEuclidean

namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open Set Metric Filter
open scoped Topology
set_option maxHeartbeats 1800000

/-- The original scalar residue evaluated on the actual inverse normal form.
The pole shift estimate is discharged by P.t_pole; it is not a new premise. -/
theorem exists_actual_regularResidue_error (B rootB : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) (hB : AnalyticAt ℂ B 0) (hBn : B 0≠0)
    (hroot : AnalyticAt ℂ rootB 0) (hrootn : rootB 0≠0)
    (r C R D : ℝ) (hr : 0<r) (hC : 0<C) (hR : 0<R) (hRr : R≤r/2) (hD : 0≤D) :
    ∃ δ K : ℝ, 0<δ ∧ 0<K ∧ δ≤R/4 ∧ ∀ n : ℕ, n≠0 → ∀ d : ℂ,
      ‖d‖<δ → (n:ℝ)*‖d‖≤D →
      ∀ P : UniformProjectedWitness B phi hphi n d r C,
      ∀ J : UniformCorrectionWitness B phi hphi n d r C P R,
      ∀ y : Config n, ‖y‖<δ → ZeroMean y →
      let v := P.V (J.W y)
      let E := Real.sqrt ((n:ℝ)*absoluteEnergy y)+(n:ℝ)*absoluteEnergy y
      ‖regularResidue B rootB phi hphi d P.T v/regularResidue B rootB phi hphi d P.T 0‖≤Real.exp (K*E) ∧
      ‖regularResidue B rootB phi hphi d P.T v/regularResidue B rootB phi hphi d P.T 0-1‖≤K*E*Real.exp (K*E) := by
  obtain ⟨s,K,hs,hK,hres⟩ := exists_uniform_regularResidue_envelope B rootB phi hphi hB hBn hroot hrootn
  have he : ∀ᶠ d : ℂ in 𝓝 0, ‖1-Complex.cos d‖<s/2 := by
    apply (continuousAt_const.sub Complex.continuous_cos.continuousAt).norm.eventually_lt continuousAt_const
    simpa using (half_pos hs)
  obtain ⟨a,ha,hτ⟩ := Metric.mem_nhds_iff.mp he
  let δ := min (R/4) (min (s/16) a)
  have hδ : 0<δ := by dsimp [δ]; positivity
  have hδs : δ≤R/4 ∧ δ≤s/16 ∧ δ≤a := by
    have hh : δ≤min (R/4) (min (s/16) a) := le_rfl
    simpa only [le_min_iff] using hh
  refine ⟨δ,K*(4*(C+1)+2*D),hδ,by positivity,hδs.1,?_⟩
  intro n hn d hd hdD P J y hy hmy
  let v := P.V (J.W y)
  let q := absoluteEnergy y
  let qv := absoluteEnergy v
  let E := Real.sqrt ((n:ℝ)*q)+(n:ℝ)*q
  have hnR : 0<(n:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hyR : ‖y‖≤R/2 := by linarith [hy,hδs.1]
  have hvnorm : ‖v‖≤4*‖y‖ := (J.corrected_bounds B phi hphi d r C R P hr hR hRr).2 y hyR |>.1
  have hvr : ‖v‖<2*r := by linarith [hy,hδs.1]
  have hw := J.w_inverse y hyR
  have hm : ZeroMean v := ((P.v_inverse (J.W y) (hw.1.trans hRr)).2.2.2 (hw.2.2.2 hmy)).1
  have hpole := (P.t_pole v hvr).2 hm
  have hshift : ‖P.T v-(1-Complex.cos d)‖≤C*qv/(n:ℝ) := by
    simpa only [averageSquaredNorm,qv,absoluteEnergy,div_eq_mul_inv,mul_assoc] using hpole
  have htlip := P.t_lip v 0 hvr (by simpa using (show 0<2*r by positivity))
  rw [P.t_zero,sub_zero] at htlip
  have hτs : ‖1-Complex.cos d‖<s/2 := hτ (by simpa using hd.trans_le hδs.2.2)
  have hts : ‖P.T v‖<s := by
    have hh := norm_le_norm_sub_add (P.T v) (1-Complex.cos d)
    linarith [hy,hδs.2.1]
  have hvs : ‖v‖<s := by linarith [hy,hδs.2.1]
  have hds : ‖d‖<s := by linarith [hd,hδs.2.1]
  have hh := hres n hn d P.T P.t_zero v hts (hτs.trans (by linarith)) hds hvs
  have hq := absoluteEnergy_nonneg y
  have hqv := absoluteEnergy_nonneg v
  have henergy := (J.corrected_energy_bounds hn B phi hphi d r C R P hRr y hyR hmy).2
  have hvenergy : qv≤4*q := by
    have hadd := absoluteEnergy_add_le (v-y) y
    rw [sub_add_cancel] at hadd
    change absoluteEnergy (v-y)≤q/64 at henergy
    change qv≤2*absoluteEnergy (v-y)+2*q at hadd
    nlinarith
  have hsqrt := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hvenergy hnR.le)
  rw [show (n:ℝ)*(4*q)=4*((n:ℝ)*q) by ring,Real.sqrt_mul (by norm_num : (0:ℝ)≤4),
    show Real.sqrt (4:ℝ)=2 by norm_num] at hsqrt
  have hshiftN : (n:ℝ)^2*‖P.T v-(1-Complex.cos d)‖≤C*(n:ℝ)*qv := by
    have h := mul_le_mul_of_nonneg_left hshift (sq_nonneg (n:ℝ))
    have hid : (n:ℝ)^2*(C*qv/(n:ℝ))=C*(n:ℝ)*qv := by field_simp
    exact h.trans_eq hid
  have hdrift : (n:ℝ)*‖d‖*Real.sqrt ((n:ℝ)*qv)≤2*D*Real.sqrt ((n:ℝ)*q) := by
    have h1 := mul_le_mul_of_nonneg_right hdD (Real.sqrt_nonneg ((n:ℝ)*qv))
    have h2 := mul_le_mul_of_nonneg_left hsqrt hD
    nlinarith
  have hbudget : (n:ℝ)^2*‖P.T v-(1-Complex.cos d)‖+
      (n:ℝ)*‖d‖*Real.sqrt ((n:ℝ)*qv)+(n:ℝ)*qv≤(4*(C+1)+2*D)*E := by
    have hqN := mul_le_mul_of_nonneg_left hvenergy hnR.le
    have hCqN := mul_le_mul_of_nonneg_left hqN hC.le
    dsimp [E]
    nlinarith [mul_nonneg hD (mul_nonneg hnR.le hq),
      mul_nonneg (show 0≤C+1 by positivity) (Real.sqrt_nonneg ((n:ℝ)*q))]
  have hfinal := exponential_envelope_mono _ (show 0≤K*((n:ℝ)^2*‖P.T v-(1-Complex.cos d)‖+
      (n:ℝ)*‖d‖*Real.sqrt ((n:ℝ)*qv)+(n:ℝ)*qv) by positivity)
    (mul_le_mul_of_nonneg_left hbudget hK.le) hh.1 hh.2
  simpa only [v,E,q,mul_assoc] using hfinal

end
end IsingBulk.Anisotropic.NegativeNormalForm
