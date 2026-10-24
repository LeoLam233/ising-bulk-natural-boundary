import IsingBulk.Anisotropic.NegativeDominance.PhysicalCompleteBoundaryJets
import IsingBulk.Anisotropic.NegativeDominance.ScaledPeriodAllJetMajorant
import IsingBulk.Anisotropic.NegativeDominance.BoundaryJetsComposition

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open IsingBulk.Anisotropic.RegularEdges Set Filter
open scoped Topology

/-- Actual complete weighted HT boundary jets in any analytic temperature
coordinate. The derivative conversion and its all-index envelope are derived. -/
theorem physical_scaled_high_series_reparametrized_boundary_jets
    {ι : Type*} {l : Filter ι} [NeBot l] {path : ι → ℂ}
    {lam b : ℝ} {B S A zeta f : ℂ → ℂ} {U V : Set ℂ}
    (hlam : 0<lam) (hb : |b|<1) (hB0 : 0<(B 0).im) (hBa : AnalyticAt ℂ B 0)
    (hSa : AnalyticAt ℂ S 0) (hSzero : S 0≠0)
    (hAa0 : AnalyticAt ℂ A 0) (hA0 : A 0≠0)
    (hzeta : AnalyticAt ℂ zeta 0)
    (hSedge : spectralS (zeta 0)≠0)
    (hedge : spectralA lam (zeta 0)+spectralT lam (zeta 0)=(b : ℂ)*spectralS (zeta 0))
    (hBedge : 0<(-spectralT lam (zeta 0)/spectralS (zeta 0)).im)
    (hU : IsOpen U) (ha : AnalyticOnNhd ℂ zeta U) (hAa : AnalyticOnNhd ℂ A U)
    (hzH : ∀ u∈U, zeta u∈omegaH lam\{0})
    (hS0 : ∀ u∈U, spectralS (zeta u)≠0)
    (hB : ∀ u∈U, B u= -spectralT lam (zeta u)/spectralS (zeta u))
    (hS : ∀ u∈U, S u=spectralS (zeta u))
    (he : ∀ u∈U, edgeMapV lam (-1) (zeta u)=(b : ℂ)+u)
    (hup : ∀ u∈U, 0<u.im) (hBi : ∀ u∈U, 0<(B u).im)
    (hAsq : ∀ u∈U, (A u)^2=spectralProduct lam (zeta u))
    (hAne : ∀ u∈U, A u≠0)
    (hV : IsOpen V) (hf : AnalyticOnNhd ℂ f V)
    (hf0 : AnalyticAt ℂ f 0) (hfz : f 0=0) (hmap : MapsTo f V U)
    (hp : Tendsto path l (𝓝 0)) (hin : ∀ᶠ t in l, path t∈V) (j : ℕ) :
    Summable (fun n : ℕ => ‖iteratedDeriv j
      (fun z => (A (f z))^(2*n+1)*continuedAngularCoefficient (2*n) lam (zeta (f z))) 0‖) ∧
    Tendsto (fun t => iteratedDeriv j (fun z => A (f z)*
      ∑' n : ℕ, (spectralProduct lam (zeta (f z)))^n*
        FormFactors.unscaledFullCoefficient (2*n+1) lam (zeta (f z))) (path t)) l
      (𝓝 (∑' n : ℕ, iteratedDeriv j
        (fun z => (A (f z))^(2*n+1)*continuedAngularCoefficient (2*n) lam (zeta (f z))) 0)) := by
  let g : ℕ → ℂ → ℂ := fun n u => A u*((spectralProduct lam (zeta u))^n*
    FormFactors.unscaledFullCoefficient (2*n+1) lam (zeta u))
  let h : ℕ → ℂ → ℂ := fun n u => (A u)^(2*n+1)*continuedAngularCoefficient (2*n) lam (zeta u)
  let F : ℂ → ℂ := fun u => A u*∑' n : ℕ, (spectralProduct lam (zeta u))^n*
    FormFactors.unscaledFullCoefficient (2*n+1) lam (zeta u)
  have hz (u : ℂ) (hu : u∈U) : zeta u∉spectralSet lam :=
    omegaH_subset_spectral_complement hlam (hzH u hu).1
  have hperiod (n : ℕ) (u : ℂ) (hu : u∈U) : g n u=
      negativeShiftedPeriod b B (fun v => S v/A v) (2*n) u := by
    dsimp only [g]
    rw [weighted_fullCoefficient_eq_scaledPeriod n hlam (hzH u hu) (hB u hu)
      (hS u hu) (he u hu) (hup u hu) (hBi u hu) (hAsq u hu) (hAne u hu)]
    rw [←mul_assoc,mul_inv_cancel₀ (hAne u hu),one_mul]
  have heq (n : ℕ) (u : ℂ) (hu : u∈U) : g n u=h n u := by
    rw [hperiod n u hu,negativeShiftedPeriod_div_scale,
      ←continuedAngularCoefficient_eq_negativeShiftedPeriod (2*n) (hB u hu) (hS u hu)
        (he u hu) (hup u hu) (hBi u hu)]
  have hg (n : ℕ) : AnalyticOnNhd ℂ (g n) U := fun u hu =>
    (hAa u hu).mul ((((FormFactors.spectralProduct_analyticAt_ff lam (zeta u)).comp (ha u hu)).pow n).mul
      ((FormFactors.unscaledFullCoefficient_analyticOnNhd (2*n+1) (by omega) lam (zeta u) (hz u hu)).comp (ha u hu)))
  have hh (n : ℕ) : AnalyticAt ℂ (h n) 0 :=
    (hAa0.pow (2*n+1)).mul ((continuedAngularCoefficient_negative_analyticAt (2*n)
      (show Odd (2*n+1) from ⟨n,by omega⟩) hSedge hedge hb hBedge).comp hzeta)
  have hfp : Tendsto (fun t => f (path t)) l (𝓝 0) := by
    simpa only [hfz,Function.comp_def] using hf0.continuousAt.tendsto.comp hp
  have hfin : ∀ᶠ t in l, f (path t)∈U := hin.mono (fun _ ht => hmap ht)
  have henv (i : ℕ) : ∃ G : ℕ → ℝ, Summable G ∧ ∀ᶠ t in l, ∀ n,
      ‖iteratedDeriv i (g n) (f (path t))‖≤G n := by
    obtain ⟨G,hG,hbound⟩ := scaledNegativePeriod_all_jet_majorant_upper
      hb hB0 hBa hSa hSzero hAa0 hA0 hzeta hSedge hedge hBedge hU ha hAa hz hS0
      hB hS he hup hBi hfp hfin i
    refine ⟨G,hG,?_⟩
    filter_upwards [hfin,hbound] with t ht hbnd n
    have hevent : g n =ᶠ[𝓝 (f (path t))] negativeShiftedPeriod b B (fun v => S v/A v) (2*n) := by
      filter_upwards [hU.mem_nhds ht] with u hu
      exact hperiod n u hu
    rw [hevent.iteratedDeriv_eq i]
    exact hbnd n
  have hfull (k : ℕ) (x : ℂ) (hx : x∈V) : HasSum
      (fun n => iteratedDeriv k (fun z => g n (f z)) x)
      (iteratedDeriv k (fun z => F (f z)) x) :=
    FormFactors.high_particleSeries_mul_comp_hasSum_iteratedDeriv lam
      ((hAa _ (hmap hx)).comp (hf x hx)) ((ha _ (hmap hx)).comp (hf x hx)) (hz _ (hmap hx)) k
  exact complete_boundary_jets_comp hV hU hf hf0 hfz hg hh hmap heq hp hin henv hfull j

end
end IsingBulk.Anisotropic.NegativeDominance
