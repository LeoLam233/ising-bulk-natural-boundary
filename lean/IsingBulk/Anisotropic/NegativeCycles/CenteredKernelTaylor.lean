import IsingBulk.Anisotropic.NegativeCycles.CenteredWitnessRemainder
import IsingBulk.Anisotropic.NegativeCycles.ActualCenteredPoleIntegral

noncomputable section
namespace IsingBulk.Anisotropic.NegativeCycles
open IsingBulk.First IsingBulk.Anisotropic.NegativeNormalForm Set MeasureTheory Metric Filter
open scoped Topology
set_option maxHeartbeats 1000000

def centeredKernelIntegral (B rootB : ℂ→ℂ) (phi : ℝ) (hphi : Real.sin phi≠0)
    (m : ℕ) (d s : ℝ) (t : ℂ) : ℂ :=
  ∫q in centeredInnerSet (2*m) d s,
    formFactorNumerator B rootB phi hphi (d:ℂ) t (shapeExtend (complexify (2*m) q))*
      cothHalf (fun u => poleEquation B phi hphi (d:ℂ) u (shapeExtend (complexify (2*m) q))) t

/-- Exact Taylor decomposition of the literal winding kernel integral. The same actual
remainder supplies the pole identity, integrability, analytic extension and jet bound. -/
theorem exists_centered_kernel_taylor (B rootB : ℂ→ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) (hB : AnalyticAt ℂ B 0) (hB0 : B 0≠0)
    (hrB : AnalyticAt ℂ rootB 0) (r C R : ℝ) (hr : 0<r) (hR : 0<R) (hRr : R≤r/2) :
    ∃(R₀ : ℂ→ℂ) (ρ c σ K M : ℝ),0<ρ ∧ 0<c ∧ 0<σ ∧ 0<K ∧ 1≤M ∧
      ∀m : ℕ, ∀d : ℝ,|d|<ρ → d≠0 →
      ∀P : UniformProjectedWitness B phi hphi (2*m+1) (d:ℂ) r C,
      ∀_J : UniformCorrectionWitness B phi hphi (2*m+1) (d:ℂ) r C P R,
      ∀s : ℝ,s<σ →
      let F := centeredInnerRemainder B rootB phi hphi R₀ m d s P.T
      AnalyticOnNhd ℂ F (ball 0 (c/(2*m+1:ℕ))) ∧
      (∀j : ℕ,‖iteratedDeriv j F 0/(j.factorial:ℂ)‖≤
        ((volume (centeredInnerSet (2*m) d s)).toReal*(K*remainderGaussianEnvelope M m))/
          ((c/(2*m+1:ℕ))/2)^j) ∧
      (∀j : ℕ,IntegrableOn (fun q => constrainedResidueDensity B rootB phi hphi (d:ℂ) P.T j
          (complexify (2*m) q)) (centeredInnerSet (2*m) d s) ∧
        iteratedDeriv j (centeredKernelIntegral B rootB phi hphi m d s) 0/(j.factorial:ℂ)=
          (∫q in centeredInnerSet (2*m) d s,
            constrainedResidueDensity B rootB phi hphi (d:ℂ) P.T j (complexify (2*m) q))+
          iteratedDeriv j F 0/(j.factorial:ℂ)) := by
  obtain ⟨R₀,a,c,sigma,K,M,ha,hc,hsigma,hK,hM,hw⟩ :=
    exists_centered_witness_remainder B rootB phi hphi hB hB0 hrB r C hr
  obtain ⟨b,hb,hp⟩ := actual_centered_pole_integral B rootB phi hphi hB hrB hB0 r C R hr hR hRr
  refine ⟨R₀,min a b,c,min sigma (b^2),K,M,lt_min ha hb,hc,
    lt_min hsigma (sq_pos_of_pos hb),hK,hM,?_⟩
  intro m d hd hd0 P J s hs
  have hw' := hw m d (hd.trans_le (min_le_left _ _)) P s (hs.trans_le (min_le_left _ _))
  obtain ⟨δ,hδ,hgap,han,hint,hjets⟩ := hp m d (hd.trans_le (min_le_right _ _)) hd0 P J s
    (hs.le.trans (min_le_right _ _))
  refine ⟨hw'.1,hw'.2.1,?_⟩
  let F := centeredInnerRemainder B rootB phi hphi R₀ m d s P.T
  let G := centeredPoleIntegral B rootB phi hphi m d s P.T
  have hcn : 0<c/(2*m+1:ℕ) := div_pos hc (by positivity)
  have hfe : centeredKernelIntegral B rootB phi hphi m d s =ᶠ[𝓝 0] (fun t => G t+F t) := by
    filter_upwards [ball_mem_nhds (0:ℂ) (lt_min hδ hcn)] with t ht
    have htδ : ‖t‖<δ := (mem_ball_zero_iff.mp ht).trans_le (min_le_left _ _)
    have htc : t∈ball 0 (c/(2*m+1:ℕ)) := mem_ball_zero_iff.mpr
      ((mem_ball_zero_iff.mp ht).trans_le (min_le_right _ _))
    have heq := hw'.2.2.2.1
    change (∫q in centeredInnerSet (2*m) d s,_)=_+_
    dsimp only [G,F,centeredPoleIntegral,centeredInnerRemainder]
    rw [←integral_add (hint t htδ) (hw'.2.2.2.2 t htc)]
    apply setIntegral_congr_fun (centeredInnerSet_measurable _ _ _)
    intro q hq
    exact heq q hq t htc (by
      intro hte
      have := hgap q hq
      rw [←hte] at this
      linarith)
  have hGa : AnalyticAt ℂ G 0 := han 0 (mem_ball_self hδ)
  have hFa : AnalyticAt ℂ F 0 := hw'.1 0 (mem_ball_self hcn)
  intro j
  refine ⟨(hjets j).1,?_⟩
  rw [hfe.iteratedDeriv_eq j]
  change iteratedDeriv j (G+F) 0/(j.factorial:ℂ)=_
  rw [iteratedDeriv_add hGa.contDiffAt hFa.contDiffAt,add_div,(hjets j).2]

end IsingBulk.Anisotropic.NegativeCycles
