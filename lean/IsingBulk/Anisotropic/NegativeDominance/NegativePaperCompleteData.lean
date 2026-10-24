import IsingBulk.Anisotropic.NegativeDominance.GrowingLowSum
import IsingBulk.Anisotropic.NegativeDominance.NonresonantBoundaryCauchy
import IsingBulk.Anisotropic.NegativeDominance.PaperReparametrization
import IsingBulk.Anisotropic.NegativeDominance.ReparametrizedPhysicalJets

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open IsingBulk.Anisotropic.RegularEdges Set Filter Metric
open scoped Topology

/-- Complete physical HT jets in the actual manuscript t-coordinate, with
u=(T/S)t and inward t=-ε, retaining the actual physical-side inclusion. -/
theorem exists_negative_paper_complete_data {lam : ℝ} (hlam : 0<lam) {z : ℂ}
    (hz : z∈frontier (omegaH lam)) (hd : spectralDet lam z<0)
    (hv : spectralV lam z= -1) (hu : |spectralU lam z|<1)
    (hder : deriv (edgeMapV lam (-1)) z≠0) (p : ℕ) (hp2 : 2≤p)
    (hphase : IsPrimitiveRoot (IsingBulk.Tail.continuedRoot (spectralU lam z : ℂ)) p) :
    ∃ zeta A : ℂ → ℂ, zeta 0=z ∧ AnalyticAt ℂ zeta 0 ∧
      AnalyticAt ℂ A 0 ∧ A 0≠0 ∧
      (∀ᶠ t in 𝓝 (0 : ℂ), A t^2=spectralProduct lam (zeta t) ∧
        edgeMapV lam (-1) (zeta t)=(spectralU lam z : ℂ)+
          (spectralT lam (zeta t)/spectralS (zeta t))*t) ∧
      (∀ᶠ ε : ℝ in 𝓝[>] 0, zeta (-(ε : ℂ))∈omegaH lam\{0}) ∧
      (∃ Z f : ℂ→ℂ, ∃r : ℝ, 0<r ∧ Z 0=z ∧ f 0=0 ∧
        AnalyticOnNhd ℂ Z (ball 0 r) ∧ AnalyticAt ℂ f 0 ∧
        zeta=(fun t => Z (f t)) ∧
        (∀u∈ball 0 r,0<u.im → Z u∈omegaH lam\{0}) ∧
        (∀ᶠ ε : ℝ in 𝓝[>] 0, f (-(ε : ℂ))∈ball 0 r ∧ 0<(f (-(ε : ℂ))).im) ∧
        A=(fun t => negativeChartRoot lam Z (f t)) ∧
        AnalyticOnNhd ℂ (negativeChartRoot lam Z) (ball 0 r) ∧
        ∀u∈ball 0 r, 0<(negativeChartB lam Z u).im ∧ spectralS (Z u)≠0 ∧
          negativeChartRoot lam Z u≠0 ∧
          edgeMapV lam (-1) (Z u)=(spectralU lam z:ℂ)+u ∧
          (0<u.im → Z u∈omegaH lam\{0})) ∧
      (∀ j : ℕ,
        Summable (fun n : ℕ => ‖iteratedDeriv j
          (fun t => A t^(2*n+1)*continuedAngularCoefficient (2*n) lam (zeta t)) 0‖) ∧
        Tendsto (fun ε : ℝ => iteratedDeriv j (fun t => A t*
          ∑' n : ℕ, (spectralProduct lam (zeta t))^n*
            FormFactors.unscaledFullCoefficient (2*n+1) lam (zeta t)) (-(ε : ℂ)))
          (𝓝[>] 0) (𝓝 (∑' n : ℕ, iteratedDeriv j
            (fun t => A t^(2*n+1)*continuedAngularCoefficient (2*n) lam (zeta t)) 0))) ∧
      (∃ a D : ℝ,0<a ∧ 0<D ∧ ∀ j n : ℕ,Odd (n+1) →
        ‖iteratedDeriv j (fun t => A t^(n+1)*continuedAngularCoefficient n lam (zeta t)) 0/(j.factorial:ℂ)‖≤
          D*((n+1:ℕ):ℝ)^2*(((n+1:ℕ):ℝ)^3/a)^j) ∧
      (∃ a r C M K : ℝ,0<a ∧ 0<r ∧ r<1 ∧ 0<C ∧ 0<M ∧ 0<K ∧
        ∀ j n : ℕ,Odd (n+1) → ¬p∣n+1 →
          ‖iteratedDeriv j (fun t => A t^(n+1)*continuedAngularCoefficient n lam (zeta t)) 0‖≤
            (j.factorial:ℝ)*(K*particleEdgeMajorant r C M (n+1))/(a/((n+1:ℕ):ℝ))^j) := by
  obtain ⟨zeta,r,hr,hz0,hza,hAa,hdata⟩ := exists_negative_chart_data hlam hz hd hv hu hder
  have h0 : (0 : ℂ)∈ball 0 r := mem_ball_self hr
  have hSa := negativeChartS_analyticAt (hza 0 h0)
  have hS0 := (hdata 0 h0).2.1
  have hP : spectralProduct lam (zeta 0)≠0 := by
    apply mul_ne_zero hS0
    rw [hz0]
    exact spectralT_ne_zero_of_det_ne_zero hd.ne
  have hBa := negativeChartB_analyticAt (lam := lam) (hza 0 h0) hS0
  have hB0 := (hdata 0 h0).1
  have hA0 := (hdata 0 h0).2.2.1
  have hedge : spectralA lam (zeta 0)+spectralT lam (zeta 0)=
      (spectralU lam z : ℂ)*spectralS (zeta 0) := by
    rw [hz0,spectral_reconstruction hd.ne,hv]
    simp only [Complex.ofReal_neg,Complex.ofReal_one]
    ring
  let U : Set ℂ := ball 0 r ∩ {u : ℂ | 0<u.im}
  have hU : IsOpen U := isOpen_ball.inter (isOpen_lt continuous_const Complex.continuous_im)
  have hzu : AnalyticOnNhd ℂ zeta U := fun u hu => hza u hu.1
  have hAu : AnalyticOnNhd ℂ (negativeChartRoot lam zeta) U := fun u hu => hAa u hu.1
  have hzH : ∀ u∈U, zeta u∈omegaH lam\{0} := fun u hu => (hdata u hu.1).2.2.2.2 hu.2
  have hSu : ∀ u∈U, spectralS (zeta u)≠0 := fun u hu => (hdata u hu.1).2.1
  have hBu : ∀ u∈U, negativeChartB lam zeta u= -spectralT lam (zeta u)/spectralS (zeta u) := fun _ _ => rfl
  have hSdef : ∀ u∈U, negativeChartS zeta u=spectralS (zeta u) := fun _ _ => rfl
  have he : ∀ u∈U, edgeMapV lam (-1) (zeta u)=(spectralU lam z : ℂ)+u :=
    fun u hu => (hdata u hu.1).2.2.2.1
  have hup : ∀ u∈U, 0<u.im := fun _ hu => hu.2
  have hBi : ∀ u∈U, 0<(negativeChartB lam zeta u).im := fun u hu => (hdata u hu.1).1
  have hAne : ∀ u∈U, negativeChartRoot lam zeta u≠0 := fun u hu => (hdata u hu.1).2.2.1
  have hAsq : ∀ u∈U, (negativeChartRoot lam zeta u)^2=spectralProduct lam (zeta u) :=
    fun u _ => negativeChartRoot_sq hP u
  obtain ⟨f,hfa,hf0,_,hpaper⟩ := exists_negative_paper_reparametrization hBa hB0
  let V : Set ℂ := {t | AnalyticAt ℂ f t ∧ f t∈U}
  have hV : IsOpen V := by
    rw [isOpen_iff_mem_nhds]
    intro t ht
    exact ht.1.eventually_analyticAt.and (ht.1.continuousAt.tendsto.eventually (hU.mem_nhds ht.2))
  have hf : AnalyticOnNhd ℂ f V := fun _ ht => ht.1
  have hmap : MapsTo f V U := fun _ ht => ht.2
  have hp : Tendsto (fun ε : ℝ => -(ε : ℂ)) (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous (fun ε : ℝ => -(ε : ℂ)) := Complex.continuous_ofReal.neg
    simpa only [Complex.ofReal_zero,neg_zero] using
      (hc.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
  have hfp : Tendsto (fun ε : ℝ => f (-(ε : ℂ))) (𝓝[>] 0) (𝓝 0) := by
    simpa only [hf0,Function.comp_def] using hfa.continuousAt.tendsto.comp hp
  have hin : ∀ᶠ ε : ℝ in 𝓝[>] 0, -(ε : ℂ)∈V := by
    filter_upwards [hp.eventually hfa.eventually_analyticAt,
      hfp.eventually (ball_mem_nhds (0 : ℂ) hr),hp.eventually hpaper,self_mem_nhdsWithin]
      with ε ha hb hpaper hpos
    refine ⟨ha,hb,?_⟩
    rw [hpaper.2]
    simpa only [mem_ofPred_eq,neg_mul_neg,Complex.mul_im,Complex.ofReal_im,mul_zero,
      Complex.ofReal_re,zero_add] using mul_pos hpaper.1 hpos
  have hfb : ∀ᶠ t in 𝓝 (0 : ℂ), f t∈ball 0 r := by
    apply hfa.continuousAt.tendsto.eventually
    change ball 0 r∈𝓝 (f 0)
    rw [hf0]
    exact ball_mem_nhds (0 : ℂ) hr
  obtain ⟨a,rC,C,M,K,haR,hrC,hrC1,hC,hM,hK,hcb⟩ :=
    scaled_negative_boundary_cauchy_all_particles hu hB0 hBa hSa hS0 (hAa 0 h0) hA0
      (hza 0 h0) hS0 hedge hB0 hU hzu hAu
      (fun u hu => omegaH_subset_spectral_complement hlam (hzH u hu).1) hSu
      hBu hSdef he hup hBi hV hf hfa hf0 hmap hp hin
  obtain ⟨D,hD,hcoeff⟩ := normalized_particle_cauchy_bound haR hrC hrC1 hC hM hK
    (fun n t => (negativeChartRoot lam zeta (f t))^(n+1)*continuedAngularCoefficient n lam (zeta (f t))) hcb
  have hnonres := scaled_negative_nonresonant_boundary_cauchy hp2 hphase
    hu hB0 hBa hSa hS0 (hAa 0 h0) hA0 (hza 0 h0) hS0 hedge hB0 hU hzu hAu
    (fun u hu => omegaH_subset_spectral_complement hlam (hzH u hu).1) hSu
    hBu hSdef he hup hBi hV hf hfa hf0 hmap hp hin
  refine ⟨fun t => zeta (f t),fun t => negativeChartRoot lam zeta (f t),?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [hf0] using hz0
  · exact (hza 0 h0).comp_of_eq hfa hf0
  · exact (hAa 0 h0).comp_of_eq hfa hf0
  · simpa only [hf0] using hA0
  · filter_upwards [hfb,hpaper] with t ht hpt
    refine ⟨negativeChartRoot_sq hP (f t),?_⟩
    rw [(hdata (f t) ht).2.2.2.1]
    calc
      (spectralU lam z : ℂ)+f t = (spectralU lam z : ℂ)+ -negativeChartB lam zeta (f t)*t :=
        congrArg (fun u => (spectralU lam z : ℂ)+u) hpt.2
      _ = _ := by simp only [negativeChartB,neg_div,neg_neg]
  · filter_upwards [hin] with ε hε
    exact hzH _ hε.2
  · refine ⟨zeta,f,r,hr,hz0,hf0,hza,hfa,rfl,?_,?_,rfl,hAa,hdata⟩
    · exact fun u hu hi => hzH u ⟨hu,hi⟩
    · filter_upwards [hin] with ε hε
      exact hε.2
  refine ⟨?_,⟨a,D,haR,hD,hcoeff⟩,hnonres⟩
  intro j
  exact physical_scaled_high_series_reparametrized_boundary_jets hlam
    hu hB0 hBa hSa hS0 (hAa 0 h0) hA0 (hza 0 h0) hS0 hedge hB0 hU hzu hAu hzH hSu
    hBu hSdef he hup hBi hAsq hAne hV hf hfa hf0 hmap hp hin j

end
end IsingBulk.Anisotropic.NegativeDominance
