import IsingBulk.Preferred22.AngularAnalytic

/-! Actual uniform angular bounds on arbitrary compact exterior sets.
All constants are independent of the particle number. -/
namespace IsingBulk.Preferred22
noncomputable section
open Complex Set MeasureTheory
open scoped BigOperators Topology

theorem trace_sub_real_off_segment {s : ℂ} (hs : 1 < ‖s‖) {c : ℝ}
    (hc : c ∈ Icc (-1 : ℝ) 1) : OffRealSegment (temperatureTrace s - (c : ℂ)) := by
  simpa only [angularW, Real.cos_arccos hc.1 hc.2] using
    angularW_off_segment hs (Real.arccos c)

theorem compact_physical_root_bound {K : Set ℂ} (hK : IsCompact K)
    (hext : ∀ s ∈ K, 1 < ‖s‖) :
    ∃ q : ℝ, 0 < q ∧ q < 1 ∧ ∀ s ∈ K, ∀ θ : ℝ, ‖physicalRoot (angularW s θ)‖ ≤ q := by
  by_cases hne : K.Nonempty
  · let F : ℂ × ℝ → ℂ := fun p => physicalRoot (temperatureTrace p.1 - (p.2 : ℂ))
    have hc : ContinuousOn F (K ×ˢ Icc (-1 : ℝ) 1) := by
      intro p hp
      have hs0 : p.1 ≠ 0 := by intro hz; have h := hext p.1 hp.1; norm_num [hz] at h
      have hW : ContinuousAt (fun r : ℂ × ℝ => temperatureTrace r.1 - (r.2 : ℂ)) p :=
        (continuousAt_fst.add (continuousAt_fst.inv₀ hs0)).sub
          (Complex.continuous_ofReal.continuousAt.comp continuousAt_snd)
      exact ((physicalRoot_analyticAt (trace_sub_real_off_segment (hext p.1 hp.1) hp.2)).continuousAt.comp
        (f := fun r : ℂ × ℝ => temperatureTrace r.1 - (r.2 : ℂ)) hW).continuousWithinAt
    have hn : (K ×ˢ Icc (-1 : ℝ) 1).Nonempty :=
      hne.prod ⟨0,by norm_num⟩
    obtain ⟨p,hp,hmax⟩ := (hK.prod isCompact_Icc).exists_isMaxOn hn hc.norm
    have hnorm : ‖F p‖ < 1 := physicalRoot_inside (trace_sub_real_off_segment (hext p.1 hp.1) hp.2)
    refine ⟨(‖F p‖+1)/2, by nlinarith [norm_nonneg (F p)], by linarith, ?_⟩
    intro s hs θ
    have hb : ‖F (s,Real.cos θ)‖ ≤ ‖F p‖ :=
      hmax ⟨hs,Real.neg_one_le_cos θ,Real.cos_le_one θ⟩
    change ‖physicalRoot (angularW s θ)‖ ≤ (‖F p‖+1)/2
    have hf : ‖physicalRoot (angularW s θ)‖ ≤ ‖F p‖ := hb
    linarith
  · refine ⟨1/2,by norm_num,by norm_num,?_⟩
    intro s hs
    exact False.elim (hne ⟨s,hs⟩)

def kernelEnvelope (q : ℝ) : ℝ := 2/(1-q^2)
def resolventEnvelope (q : ℝ) : ℝ := 2/(1-q)

theorem pair_denominator_lower {q : ℝ} (hq0 : 0 ≤ q) {u v : ℂ}
    (hu : ‖u‖ ≤ q) (hv : ‖v‖ ≤ q) : 1-q^2 ≤ ‖1-u*v‖ := by
  have hp : ‖u*v‖ ≤ q^2 := by
    rw [norm_mul,pow_two]
    exact mul_le_mul hu hv (norm_nonneg _) hq0
  have h := norm_sub_norm_le (1 : ℂ) (u*v)
  rw [norm_one] at h
  linarith

theorem sqrt_ratio_norm_le_one {q : ℝ} (hq1 : q < 1) {y z : ℂ}
    (hy : ‖y‖ = 1) (hz : ‖z‖ ≤ q) : ‖Complex.sqrt (z/y)‖ ≤ 1 := by
  have hs : ‖Complex.sqrt (z/y)‖^2 = ‖z‖ := by
    rw [← norm_pow,complex_sqrt_sq,norm_div,hy,div_one]
  nlinarith [norm_nonneg (Complex.sqrt (z/y))]

theorem gaugeKernel_norm_bound {N : ℕ} {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (y z : Fin N → ℂ) (hy : ∀ i, ‖y i‖ = 1) (hz : ∀ i, ‖z i‖ ≤ q) (i j : Fin N) :
    ‖gaugeKernel y z i j‖ ≤ kernelEnvelope q := by
  have hD : 0 < 1-q^2 := by nlinarith
  have hd := pair_denominator_lower hq0 (hz i) (hz j)
  have hi := sqrt_ratio_norm_le_one hq1 (hy i) (hz i)
  have hj := sqrt_ratio_norm_le_one hq1 (hy j) (hz j)
  have hyij : ‖y i-y j‖ ≤ 2 := by
    simpa only [hy i,hy j,one_add_one_eq_two] using norm_sub_le (y i) (y j)
  have hn : ‖Complex.sqrt (z i/y i)‖*‖Complex.sqrt (z j/y j)‖*‖y i-y j‖ ≤ 2 := by
    calc
      _ ≤ (1*1)*2 := mul_le_mul
        (mul_le_mul hi hj (norm_nonneg _) zero_le_one) hyij (norm_nonneg _) (by norm_num)
      _ = 2 := by norm_num
  unfold gaugeKernel kernelEnvelope
  rw [norm_div]
  simp only [norm_mul,norm_neg,Complex.norm_I,one_mul]
  exact (div_le_div_of_nonneg_right hn (norm_nonneg _)).trans
    (div_le_div_of_nonneg_left (by norm_num) hD hd)

theorem oneBody_norm_bound {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) {z : ℂ}
    (hz : ‖z‖ ≤ q) : ‖oneBody z‖ ≤ kernelEnvelope q := by
  have hD : 0 < 1-q^2 := by nlinarith
  have hd : 1-q^2 ≤ ‖1-z^2‖ := by simpa only [pow_two] using pair_denominator_lower hq0 hz hz
  have hn : 2*‖z‖ ≤ 2 := by linarith
  simp only [oneBody,kernelEnvelope,norm_div,norm_mul,Complex.norm_ofNat]
  exact (div_le_div_of_nonneg_right hn (norm_nonneg _)).trans
    (div_le_div_of_nonneg_left (by norm_num) hD hd)

theorem product_norm_le_q {N : ℕ} (hN : 0 < N) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (z : Fin N → ℂ) (hz : ∀ i, ‖z i‖ ≤ q) : ‖∏ i, z i‖ ≤ q := by
  have hp : ‖∏ i, z i‖ ≤ q^N := by
    rw [norm_prod]
    calc
      _ ≤ ∏ _i : Fin N, q := Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => hz i)
      _ = _ := by simp
  have hpow : q^N ≤ q := by
    simpa only [pow_one] using pow_le_pow_of_le_one hq0 hq1.le (show 1 ≤ N by omega)
  exact hp.trans hpow

theorem product_resolvent_norm_bound {N : ℕ} (hN : 0 < N) {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (z : Fin N → ℂ) (hz : ∀ i, ‖z i‖ ≤ q) :
    ‖(1+∏ i,z i)/(1-∏ i,z i)‖ ≤ resolventEnvelope q := by
  have hZ := product_norm_le_q hN hq0 hq1 z hz
  have hnum : ‖1+∏ i,z i‖ ≤ 2 := by
    have h := norm_add_le (1 : ℂ) (∏ i,z i)
    rw [norm_one] at h
    linarith
  have hden : 1-q ≤ ‖1-∏ i,z i‖ := by
    have h := norm_sub_norm_le (1 : ℂ) (∏ i,z i)
    rw [norm_one] at h
    linarith
  rw [norm_div]
  exact (div_le_div_of_nonneg_right hnum (norm_nonneg _)).trans
    (div_le_div_of_nonneg_left (by norm_num) (sub_pos.mpr hq1) hden)

end
end IsingBulk.Preferred22
