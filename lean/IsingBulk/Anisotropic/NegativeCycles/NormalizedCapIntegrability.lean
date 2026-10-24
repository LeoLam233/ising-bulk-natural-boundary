import IsingBulk.Anisotropic.NegativeCycles.NormalizedCapIdentity
import IsingBulk.Anisotropic.NegativeCycles.CutoffLocalization

noncomputable section
namespace IsingBulk.Anisotropic.NegativeCycles
open IsingBulk.First IsingBulk.Anisotropic.NegativeNormalForm Set MeasureTheory Metric
open scoped BigOperators

theorem constrainedJacobian_analyticAt_point {n : ℕ} (Phi : Config (n+1)→Config (n+1))
    (u : Config n) (hPhi : AnalyticAt ℂ Phi (freeChartCLM n u)) :
    AnalyticAt ℂ (constrainedJacobian Phi) u := by
  have hM : AnalyticAt ℂ (constrainedMap Phi) u :=
    ((freeCoordinatesCLM n).analyticAt _).comp (hPhi.comp ((freeChartCLM n).analyticAt u))
  have hD := hM.fderiv
  have hentry (i j : Fin n) : AnalyticAt ℂ
      (fun v=>fderiv ℂ (constrainedMap Phi) v (Pi.single j 1) i) u := by
    let L : (Config n →L[ℂ] Config n) →L[ℂ] Config n :=
      ContinuousLinearMap.apply ℂ (Config n) (Pi.single j 1)
    exact (analyticAt_pi_iff.mp ((L.analyticAt _).comp hD)) i
  have he : constrainedJacobian Phi=(fun v=>∑e : Equiv.Perm (Fin n),
      (Equiv.Perm.sign e:ℂ)*∏i,fderiv ℂ (constrainedMap Phi) v (Pi.single i 1) (e i)) := by
    funext v
    exact Matrix.det_apply' _
  rw [he]
  apply Finset.analyticAt_fun_sum
  intro e _
  apply analyticAt_const.mul
  apply Finset.analyticAt_fun_prod
  intro i _
  exact hentry _ _

/-- Compactly supported cutoff integration needs regularity only on the actual
compact support, not measurability of arbitrary inverse extensions elsewhere. -/
theorem cutoff_cap_integrable_of_local_analytic {n : ℕ} (B rootB : ℂ→ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) (d : ℂ) (T : Config (n+1)→ℂ)
    (Phi : Config (n+1)→Config (n+1)) (j : ℕ) (ρ : ℝ) (hρ : 0≤ρ)
    (b : ContDiffBump (0:ℝ)) (hb : b.rOut≤ρ^2)
    (hlocal : ∀q : Fin n→ℝ,constrainedSquaredRadius q≤ρ^2 →
      let y := freeChartCLM n (complexify n q)
      AnalyticAt ℂ Phi y ∧ ZeroMean (Phi y) ∧
      AnalyticAt ℂ (poleResidue B rootB phi hphi d T) (Phi y) ∧
      AnalyticAt ℂ T (Phi y) ∧ T (Phi y)≠0) :
    Integrable (fun q : Fin n→ℝ=>(shapeSpatialCutoff b q:ℂ)*
      constrainedResidueDensity B rootB phi hphi d T j (constrainedMap Phi (complexify n q))*
        constrainedJacobian Phi (complexify n q)) := by
  let K : Set (Fin n→ℝ) := {q | constrainedSquaredRadius q≤ρ^2}
  have hK : IsCompact K := isCompact_constrained_squared_sublevel ρ hρ
  have hcont : ContinuousOn (fun q : Fin n→ℝ=>
      constrainedResidueDensity B rootB phi hphi d T j (constrainedMap Phi (complexify n q))*
        constrainedJacobian Phi (complexify n q)) K := by
    have hg : ContinuousOn (fun q : Fin n→ℝ=>
        poleResidue B rootB phi hphi d T (Phi (freeChartCLM n (complexify n q)))*
          constrainedJacobian Phi (complexify n q)/
            T (Phi (freeChartCLM n (complexify n q)))^(j+1)) K := by
      intro q hq
      obtain ⟨hP,_hm,hN,hT,hTn⟩ := hlocal q hq
      have hPc := hP.comp ((freeChartCLM n).analyticAt (complexify n q))
      have hA := ((hN.comp (f := fun u=>Phi (freeChartCLM n u)) hPc).mul (constrainedJacobian_analyticAt_point Phi _ hP)).div
        ((hT.comp (f := fun u=>Phi (freeChartCLM n u)) hPc).pow (j+1)) (pow_ne_zero _ hTn)
      exact (hA.continuousAt.comp (complexify n).continuous.continuousAt).continuousWithinAt
    apply hg.congr
    intro q hq
    exact constrainedResidueDensity_pullback B rootB phi hphi d T j Phi _ (hlocal q hq).2.1
  have hc := (Complex.continuous_ofReal.comp (shapeSpatialCutoff_contDiff (n := n) b 0).continuous).continuousOn.mul hcont
  have hi := hc.integrableOn_compact (μ := volume) hK
  have hs : Function.support (fun q : Fin n→ℝ=>(shapeSpatialCutoff b q:ℂ)*
      (constrainedResidueDensity B rootB phi hphi d T j (constrainedMap Phi (complexify n q))*
        constrainedJacobian Phi (complexify n q)))⊆K := by
    intro q hq
    by_contra hn
    have hz := shapeSpatialCutoff_zero b (hb.trans (le_of_not_ge hn))
    exact hq (by simp [hz])
  have hh := (integrableOn_iff_integrable_of_support_subset hs).mp hi
  simpa only [mul_assoc] using hh

end IsingBulk.Anisotropic.NegativeCycles
