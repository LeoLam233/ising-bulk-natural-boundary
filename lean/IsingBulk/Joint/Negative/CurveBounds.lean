import IsingBulk.Joint.Negative.Normalization
import IsingBulk.Joint.Negative.AllParticleCauchy
import IsingBulk.Joint.Negative.NonresonantCauchy
import IsingBulk.Joint.Negative.OuterGaussian
import IsingBulk.Joint.Negative.ModelData
import IsingBulk.Anisotropic.NegativeDominance.GrowingLowSum
import IsingBulk.Anisotropic.NegativeDominance.NonresonantGaussian

/-! All-index actual curve bounds. Each Cauchy/Gaussian estimate is derived
from the proved angular integrals and the constructed coordinate change. -/
namespace IsingBulk.Joint.Negative
noncomputable section
open Set Filter Metric MeasureTheory
open IsingBulk.Anisotropic.RegularEdges IsingBulk.Anisotropic.NegativeDominance
open IsingBulk.Anisotropic.NegativeCycles
open scoped Topology BigOperators
set_option maxHeartbeats 2000000

theorem UpperNormalization.coefficient_germ {curve : ℂ→Coupling} {amp : ℂ→ℂ} {b : ℝ}
    (D : UpperNormalization curve amp b) (n : ℕ) :
    (fun t=>amp t^(n+1)*continuedAngularCoefficient n (curve t)) =ᶠ[𝓝 (0:ℂ)]
      (fun t=>D.weight (D.f t)^(n+1)*continuedAngularCoefficient n (D.Z (D.f t))) := by
  filter_upwards [D.curve_eq,D.weight_eq] with t hc ha
  rw [hc,ha]

theorem UpperNormalization.taylor_eq {curve : ℂ→Coupling} {amp : ℂ→ℂ} {b : ℝ}
    (D : UpperNormalization curve amp b) (n j : ℕ) (v : Fin n→ℝ) :
    physicalDensityTaylor n curve amp j v=
      physicalDensityTaylor n (fun t=>D.Z (D.f t)) (fun t=>D.weight (D.f t)) j v := by
  unfold physicalDensityTaylor
  congr 1
  apply Filter.EventuallyEq.iteratedDeriv_eq
  filter_upwards [D.curve_eq,D.weight_eq] with t hc ha
  simp only [weightedShiftedPhysicalDensity,hc,ha]

/-- Every odd particle, the growing low range, every nonresonant particle, and
all outer winding regions are controlled by actual Cauchy bounds. -/
theorem UpperNormalization.actual_bounds {curve : ℂ→Coupling} {amp : ℂ→ℂ} {b : ℝ}
    (D : UpperNormalization curve amp b) (hb : |b|<1)
    {p0 : ℕ} (hp : 2≤p0) (hphase : IsPrimitiveRoot (IsingBulk.Tail.continuedRoot (b:ℂ)) p0) :
    (∃a Dlow aR CR : ℝ,0<a ∧ 0<Dlow ∧ 0<aR ∧
      (∀j m,‖negativePaperParticleCoefficient curve amp m j‖≤
        Dlow*((2*m+1:ℕ):ℝ)^2*(((2*m+1:ℕ):ℝ)^3/a)^j) ∧
      (∀j m,¬p0∣2*m+1 → ‖negativePaperParticleCoefficient curve amp m j‖≤
        gaussianEnvelope aR CR (2*m+1) j)) ∧
    (∀s : ℝ,0<s → ∃g C : ℝ,0<g ∧ 0<C ∧ ∀m j : ℕ,
      ‖∫v in physicalOuterRegion (2*m) s,physicalDensityTaylor (2*m) curve amp j v‖≤
        gaussianEnvelope g C (2*m+1) j) := by
  have h0 : (0:ℂ)∈ball 0 D.radius := mem_ball_self D.radius_pos
  have hZa := D.Z_analytic 0 h0
  have hAa := D.weight_analytic 0 h0
  have hS0 := D.S_ne 0 h0
  have hA0 := D.weight_ne 0 h0
  have hBa := negativeChartB_analyticAt hZa hS0
  have hSa := negativeChartS_analyticAt hZa
  have hB0 := D.B_pos 0 h0
  have hedge : A (D.Z 0)+T (D.Z 0)=(b:ℂ)*S (D.Z 0) := by
    have he := D.edge 0 h0
    simp only [add_zero,transferC,transferB] at he
    field_simp at he
    linear_combination he
  let U : Set ℂ := upperBall D.radius
  let V : Set ℂ := {t | AnalyticAt ℂ D.f t ∧ D.f t∈U}
  have hU : IsOpen U := upperBall_isOpen _
  have hV : IsOpen V := by
    rw [isOpen_iff_mem_nhds]
    intro t ht
    exact ht.1.eventually_analyticAt.and
      (ht.1.continuousAt.tendsto.eventually (hU.mem_nhds ht.2))
  have hZ : AnalyticOnNhd ℂ D.Z U := fun u hu=>D.Z_analytic u hu.1
  have hA : AnalyticOnNhd ℂ D.weight U := fun u hu=>D.weight_analytic u hu.1
  have hS : ∀u∈U,S (D.Z u)≠0 := fun u hu=>D.S_ne u hu.1
  have hBi : ∀u∈U,0<(negativeChartB D.Z u).im := fun u hu=>D.B_pos u hu.1
  have he : ∀u∈U,transferC (D.Z u)+transferB (D.Z u)=(b:ℂ)+u := fun u hu=>D.edge u hu.1
  have hz : ∀u∈U,D.Z u∉spectralSet := by
    intro u hu
    apply outside_spectralSet_of_transferW_im_pos (hS u hu)
    exact transferW_im_pos_negative_chart (B:=negativeChartB D.Z) rfl (he u hu) hu.2 (hBi u hu)
  have hf : AnalyticOnNhd ℂ D.f V := fun _ ht=>ht.1
  have hmap : MapsTo D.f V U := fun _ ht=>ht.2
  have hpath : Tendsto (fun ε : ℝ=>-(ε:ℂ)) (𝓝[>] 0) (𝓝 0) := by
    have h : Continuous (fun ε : ℝ=>-(ε:ℂ)) := Complex.continuous_ofReal.neg
    simpa only [Complex.ofReal_zero,neg_zero] using
      (h.continuousAt (x:=0)).tendsto.mono_left nhdsWithin_le_nhds
  have hin : ∀ᶠε : ℝ in 𝓝[>] 0,-(ε:ℂ)∈V := by
    filter_upwards [D.inward,hpath.eventually D.f_analytic.eventually_analyticAt] with ε hi ha
    exact ⟨ha,hi⟩
  obtain ⟨a,r,C,M,K,ha,hr,hr1,hC,hM,hK,hcb⟩ :=
    scaled_negative_boundary_cauchy_all_particles hb hB0 hBa hSa hS0 hAa hA0 hZa hS0 hedge hB0
      hU hZ hA hz hS (fun _ _=>rfl) (fun _ _=>rfl) he (fun _ hu=>hu.2) hBi
      hV hf D.f_analytic D.f_zero hmap hpath hin
  obtain ⟨Dlow,hDlow,hlow⟩ := normalized_particle_cauchy_bound ha hr hr1 hC hM hK
    (fun n t=>D.weight (D.f t)^(n+1)*continuedAngularCoefficient n (D.Z (D.f t))) hcb
  obtain ⟨an,rn,Cn,Mn,Kn,han,hrn,hrn1,hCn,hMn,hKn,hn⟩ :=
    scaled_negative_nonresonant_boundary_cauchy hp hphase hb hB0 hBa hSa hS0 hAa hA0 hZa hS0 hedge hB0
      hU hZ hA hz hS (fun _ _=>rfl) (fun _ _=>rfl) he (fun _ hu=>hu.2) hBi
      hV hf D.f_analytic D.f_zero hmap hpath hin
  obtain ⟨aR,CR,haR,_hCR,hng⟩ := nonresonant_cauchy_gaussian han hrn hrn1 hCn hMn hKn p0
    (fun n t=>D.weight (D.f t)^(n+1)*continuedAngularCoefficient n (D.Z (D.f t))) hn
  constructor
  · refine ⟨a,Dlow,aR,CR,ha,hDlow,haR,?_,?_⟩
    · intro j m
      unfold negativePaperParticleCoefficient
      rw [(D.coefficient_germ (2*m)).iteratedDeriv_eq j]
      exact hlow j (2*m) ⟨m,by omega⟩
    · intro j m hm
      unfold negativePaperParticleCoefficient
      rw [(D.coefficient_germ (2*m)).iteratedDeriv_eq j]
      simpa only [gaussianEnvelope,Nat.cast_add,Nat.cast_one] using
        hng j (2*m) ⟨m,by omega⟩ hm
  · intro s hs
    obtain ⟨g,C,hg,hC,ho⟩ := physical_outer_jet_gaussian D.radius_pos hZa hAa hA0 hS0 hedge hb hB0
      D.f_analytic D.f_zero (fun u hu=>⟨D.edge u hu.1,D.B_pos u hu.1⟩) D.inward s hs
    refine ⟨g,C,hg,hC,?_⟩
    intro m j
    simp_rw [D.taylor_eq]
    exact ho m j

end
end IsingBulk.Joint.Negative
