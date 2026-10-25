import IsingBulk.Joint.Negative.AllJetMajorant
import IsingBulk.Joint.RegularEdges.PhysicalIdentity
import IsingBulk.Joint.FormFactors.CurveJets
import IsingBulk.Anisotropic.NegativeDominance.BoundaryJetsComposition

namespace IsingBulk.Joint.Negative
noncomputable section
open IsingBulk.Anisotropic.NegativeDominance IsingBulk.Anisotropic.RegularEdges Set Filter
open scoped Topology

/-- Actual complete weighted HT boundary jets in any analytic temperature
coordinate. The derivative conversion and its all-index envelope are derived. -/
theorem physical_scaled_high_series_reparametrized_boundary_jets
    {ι : Type*} {l : Filter ι} [NeBot l] {path : ι → ℂ}
    {b : ℝ} {B S amp f : ℂ → ℂ} {curve : ℂ → Coupling} {U V : Set ℂ}
    (hb : |b|<1) (hB0 : 0<(B 0).im) (hBa : AnalyticAt ℂ B 0)
    (hSa : AnalyticAt ℂ S 0) (hSzero : S 0≠0)
    (hAa0 : AnalyticAt ℂ amp 0) (hA0 : amp 0≠0)
    (hzeta : AnalyticAt ℂ curve 0)
    (hSedge : IsingBulk.Joint.S (curve 0)≠0)
    (hedge : IsingBulk.Joint.A (curve 0)+T (curve 0)=(b : ℂ)*IsingBulk.Joint.S (curve 0))
    (hBedge : 0<(-T (curve 0)/IsingBulk.Joint.S (curve 0)).im)
    (hU : IsOpen U) (ha : AnalyticOnNhd ℂ curve U) (hAa : AnalyticOnNhd ℂ amp U)
    (hzH : ∀ u∈U, curve u∈highDomain)
    (hS0 : ∀ u∈U, IsingBulk.Joint.S (curve u)≠0)
    (hB : ∀ u∈U, B u= -T (curve u)/IsingBulk.Joint.S (curve u))
    (hS : ∀ u∈U, S u=IsingBulk.Joint.S (curve u))
    (he : ∀ u∈U, transferC (curve u)+transferB (curve u)=(b : ℂ)+u)
    (hup : ∀ u∈U, 0<u.im) (hBi : ∀ u∈U, 0<(B u).im)
    (hAsq : ∀ u∈U, (amp u)^2=p (curve u))
    (_hAne : ∀ u∈U, amp u≠0)
    (hV : IsOpen V) (hf : AnalyticOnNhd ℂ f V)
    (hf0 : AnalyticAt ℂ f 0) (hfz : f 0=0) (hmap : MapsTo f V U)
    (hp : Tendsto path l (𝓝 0)) (hin : ∀ᶠ t in l, path t∈V) (j : ℕ) :
    Summable (fun n : ℕ => ‖iteratedDeriv j
      (fun z => (amp (f z))^(2*n+1)*continuedAngularCoefficient (2*n) (curve (f z))) 0‖) ∧
    Tendsto (fun t => iteratedDeriv j (fun z => amp (f z)*
      ∑' n : ℕ, (p (curve (f z)))^n*
        FormFactors.unscaledFullCoefficient (2*n+1) (curve (f z))) (path t)) l
      (𝓝 (∑' n : ℕ, iteratedDeriv j
        (fun z => (amp (f z))^(2*n+1)*continuedAngularCoefficient (2*n) (curve (f z))) 0)) := by
  let g : ℕ → ℂ → ℂ := fun n u => amp u*((p (curve u))^n*
    FormFactors.unscaledFullCoefficient (2*n+1) (curve u))
  let h : ℕ → ℂ → ℂ := fun n u => (amp u)^(2*n+1)*continuedAngularCoefficient (2*n) (curve u)
  let F : ℂ → ℂ := fun u => amp u*∑' n : ℕ, (p (curve u))^n*
    FormFactors.unscaledFullCoefficient (2*n+1) (curve u)
  have hz (u : ℂ) (hu : u∈U) : curve u∉spectralSet :=
    highDomain_subset_spectralComplement (hzH u hu)
  have heq (n : ℕ) (u : ℂ) (hu : u∈U) : g n u=h n u := by
    dsimp only [g,h]
    rw [RegularEdges.fullCoefficient_eq_physicalAngular_high (2*n) (hzH u hu) (hS0 u hu),
      ←continuedAngularCoefficient_eq_unscaled_of_im_pos (2*n) (hz u hu) (hS0 u hu)
        (transferW_im_pos_negative_chart (hB u hu) (he u hu) (hup u hu) (hBi u hu)),
      ←hAsq u hu,←pow_mul,pow_succ]
    ring
  have hperiod (n : ℕ) (u : ℂ) (hu : u∈U) : g n u=
      negativeShiftedPeriod b B (fun v => S v/amp v) (2*n) u := by
    rw [heq n u hu,negativeShiftedPeriod_div_scale]
    dsimp only [h]
    rw [continuedAngularCoefficient_eq_negativeShiftedPeriod (2*n) (hB u hu)
      (hS u hu) (he u hu) (hup u hu) (hBi u hu)]
  have hg (n : ℕ) : AnalyticOnNhd ℂ (g n) U := by
    apply DifferentiableOn.analyticOnNhd _ hU
    intro u hu
    exact ((hAa u hu).differentiableAt.mul
      ((FormFactors.particleTerm_contDiffAt (fun n=>2*n+1) id (fun _=>by omega) n 1
        (hz u hu)).differentiableAt (by norm_num) |>.comp u (ha u hu).differentiableAt)).differentiableWithinAt
  have hh (n : ℕ) : AnalyticAt ℂ (h n) 0 :=
    weighted_coefficient_negative_analyticAt (2*n) ⟨n,by omega⟩ hzeta hAa0
      hSedge hedge hb hBedge
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
    have hevent : g n =ᶠ[𝓝 (f (path t))] negativeShiftedPeriod b B (fun v => S v/amp v) (2*n) := by
      filter_upwards [hU.mem_nhds ht] with u hu
      exact hperiod n u hu
    rw [hevent.iteratedDeriv_eq i]
    exact hbnd n
  have hfull (k : ℕ) (x : ℂ) (hx : x∈V) : HasSum
      (fun n => iteratedDeriv k (fun z => g n (f z)) x)
      (iteratedDeriv k (fun z => F (f z)) x) :=
    FormFactors.high_particleSeries_mul_comp_hasSum_iteratedDeriv
      ((ha _ (hmap hx)).comp (hf x hx)) ((hAa _ (hmap hx)).comp (hf x hx)) (hz _ (hmap hx)) k
  exact complete_boundary_jets_comp hV hU hf hf0 hfz hg hh hmap heq hp hin henv hfull j

end
end IsingBulk.Joint.Negative
