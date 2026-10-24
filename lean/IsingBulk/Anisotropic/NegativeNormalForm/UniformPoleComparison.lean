import IsingBulk.Anisotropic.NegativeNormalForm.UniformAngularComparison

namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open Set Filter Metric
open scoped Topology
set_option maxHeartbeats 800000

/-- Any two sufficiently small actual pole roots obey an arbitrarily small,
dimension-independent configuration Lipschitz bound. No root extension is assumed. -/
theorem negativePole_uniform_small_comparison (B : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) (hB : AnalyticAt ℂ B 0) (hB0 : B 0≠0)
    (κ : ℝ) (hκ : 0<κ) :
    ∃ δ : ℝ, 0<δ ∧ ∀ n : ℕ, n≠0 → ∀ d : ℂ, ‖d‖<δ →
      ∀ v w : Config n, ‖v‖<δ → ‖w‖<δ → ∀ t s : ℂ, ‖t‖<δ → ‖s‖<δ →
      poleEquation B phi hphi d t v=0 → poleEquation B phi hphi d s w=0 →
      ‖t-s‖≤κ*‖v-w‖ := by
  let c := centralParameterSlope B phi 0
  have hc : c≠0 := centralParameterSlope_ne_zero B phi hphi 0 (by simpa using hB0)
  let K := ‖c⁻¹‖
  have hK : 0≤K := norm_nonneg _
  let ε := κ/(2*(K+1))
  have hε : 0<ε := div_pos hκ (by positivity)
  obtain ⟨η,hη,hangular⟩ := negativePhase_uniform_angular_small B phi hphi hB ε hε
  obtain ⟨ρ,hρ,hphase⟩ := negativePhase_uniform_slope B phi hphi hB hB0
  let δ := min η (ρ/4)
  have hδ : 0<δ := lt_min hη (by positivity)
  have hδη : δ≤η := min_le_left _ _
  have hδρ : δ≤ρ/4 := min_le_right _ _
  refine ⟨δ,hδ,?_⟩
  intro n hn d hd v w hv hw t s ht hs htv hsw
  have hdata (u : ℂ) (hu : u∈closedBall 0 δ) (i : Fin n) :
      AnalyticAt ℂ (fun z : ℂ × ℂ => negativePhase B phi hphi z.1 z.2) (u,d+v i) ∧
        ‖phaseParameterSlope B phi hphi (u,d+v i)-c‖≤‖c‖/4 := by
    apply hphase
    · have hu' : ‖u‖≤δ := by simpa using hu
      linarith
    · have hi := norm_le_pi_norm v i
      have ha := norm_add_le d (v i)
      linarith
  have hLip : LipschitzOnWith (1/2) (poleNewton B phi hphi d v) (closedBall 0 δ) := by
    apply (convex_closedBall 0 δ).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (fun u hu => (poleNewton_hasDerivAt B phi hphi d u v (fun i => (hdata u hu i).1)).hasDerivWithinAt)
    intro u hu
    have hh := poleNewton_slope_norm_le hn B phi hphi d u v hc (fun i => (hdata u hu i).2)
    change ‖1-(centralParameterSlope B phi 0)⁻¹*mean (fun i => phaseParameterSlope B phi hphi (u,d+v i))‖≤(1/2:ℝ)
    linarith
  have ht' : t∈closedBall 0 δ := by simpa using ht.le
  have hs' : s∈closedBall 0 δ := by simpa using hs.le
  have hft : poleNewton B phi hphi d v t=t := by simp [poleNewton,poleAverage,htv]
  have hfs : poleNewton B phi hphi d w s=s := by simp [poleNewton,poleAverage,hsw]
  have hfirst := hLip.dist_le_mul t ht' s hs'
  simp only [dist_eq_norm,hft,NNReal.coe_div,NNReal.coe_one,NNReal.coe_ofNat] at hfirst
  have hsecond0 := poleAverage_angular_bound hn B phi hphi d s v w ε hε.le
    (fun i => hangular s d (v i) (w i) (hs.trans_le hδη) (hd.trans_le hδη)
      ((norm_le_pi_norm v i).trans_lt (hv.trans_le hδη))
      ((norm_le_pi_norm w i).trans_lt (hw.trans_le hδη)))
  have hdiff : poleNewton B phi hphi d v s-poleNewton B phi hphi d w s=
      -c⁻¹*(poleAverage B phi hphi d s v-poleAverage B phi hphi d s w) := by
    unfold poleNewton
    dsimp [c]
    ring
  have hsecond : ‖poleNewton B phi hphi d v s-s‖≤K*(ε*‖v-w‖) := by
    rw [hfs] at hdiff
    rw [hdiff,norm_mul,norm_neg]
    exact mul_le_mul_of_nonneg_left hsecond0 hK
  have htriangle := norm_sub_le_norm_sub_add_norm_sub t (poleNewton B phi hphi d v s) s
  have hscale : 2*K*ε≤κ := by
    have he : ε*(2*(K+1))=κ := by dsimp [ε]; field_simp
    nlinarith
  have hscale' := mul_le_mul_of_nonneg_right hscale (norm_nonneg (v-w))
  nlinarith

end
end IsingBulk.Anisotropic.NegativeNormalForm
