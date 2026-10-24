import IsingBulk.Anisotropic.NegativeNormalForm.PoleAverage

namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open Set Filter Metric
open scoped Topology BigOperators

theorem poleAverage_uniform_center_bounds (B : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) (hB : AnalyticAt ℂ B 0) :
    ∃ δ M : ℝ, 0<δ ∧ 0<M ∧ ∀ (n : ℕ), n≠0 → ∀ d : ℂ, ‖d‖<δ →
      ∀ v : Config n, ‖v‖<δ →
      ‖poleAverage B phi hphi d (1-Complex.cos d) v‖≤M*‖v‖ ∧
      (ZeroMean v → ‖poleAverage B phi hphi d (1-Complex.cos d) v‖≤M*averageSquaredNorm v) := by
  obtain ⟨r,L,M,hr,_,hM,hbound,_⟩ := phaseFactors_uniform_triple_bounds B phi hphi hB
  obtain ⟨s,hs,hident⟩ := Metric.mem_nhds_iff.mp (phase_factors_triple_eventually B phi hphi hB)
  let R := min r s
  have hR : 0<R := lt_min hr hs
  have ht : ∀ᶠ d : ℂ in 𝓝 0, ‖1-Complex.cos d‖<R/2 := by
    have hc : ContinuousAt (fun d : ℂ => ‖1-Complex.cos d‖) 0 := by fun_prop
    exact hc.eventually_lt continuousAt_const (by simpa using half_pos hR)
  obtain ⟨η,hη,hτ⟩ := Metric.mem_nhds_iff.mp ht
  let δ := min (R/2) η
  have hδ : 0<δ := lt_min (half_pos hR) hη
  refine ⟨δ,M,hδ,hM,?_⟩
  intro n hn d hd v hv
  have hdR : ‖d‖<R := hd.trans_le (min_le_left _ _) |>.trans (half_lt_self hR)
  have hvR : ‖v‖<R := hv.trans_le (min_le_left _ _) |>.trans (half_lt_self hR)
  have hτR : ‖1-Complex.cos d‖<R :=
    (hτ (show d∈ball (0:ℂ) η by simpa using hd.trans_le (min_le_right _ _))).trans (half_lt_self hR)
  have hp (i : Fin n) : ‖(((1-Complex.cos d),d,v i):ScalarTriple)‖<R := by
    simp only [Prod.norm_def,max_lt_iff]
    exact ⟨hτR,hdR,(norm_le_pi_norm v i).trans_lt hvR⟩
  have hi (i : Fin n) := hident (show ((1-Complex.cos d),d,v i)∈ball (0:ScalarTriple) s by
    simpa only [mem_ball,dist_zero_right] using (hp i).trans_le (min_le_right _ _))
  have hb (i : Fin n) := hbound ((1-Complex.cos d),d,v i) ((hp i).trans_le (min_le_left _ _))
  constructor
  · change ‖mean (fun i => negativePhase B phi hphi (1-Complex.cos d) (d+v i)-(phi:ℂ)*Complex.I)‖≤_
    apply (norm_mean_le hn _).trans
    apply pi_norm_le_iff_of_nonneg (mul_nonneg hM.le (norm_nonneg v)) |>.mpr
    intro i
    have hh := (hi i).1
    simp only [phaseIncrement,negativePhase_center] at hh
    rw [hh,norm_mul]
    exact (mul_le_mul_of_nonneg_left (hb i).2.2.1 (norm_nonneg _)).trans
      (by nlinarith [norm_le_pi_norm v i])
  · intro hv0
    exact poleAverage_zeroMean_bound B phi hphi d v hv0
      (fun i => (hi i).1) (fun i => (hi i).2) (fun i => (hb i).2.2.2)

end
end IsingBulk.Anisotropic.NegativeNormalForm
