import IsingBulk.Joint.Negative.PhysicalBoundaryJets
import IsingBulk.Joint.Negative.HighSide
import IsingBulk.Joint.Negative.CurveBounds

namespace IsingBulk.Joint.Negative
noncomputable section
open Set Filter Metric IsingBulk.Anisotropic.RegularEdges
open scoped Topology

/-- The complete actual HT contour sum has all boundary jets given by the
complete continued angular sum, on a constructed open physical overlap. -/
theorem UpperNormalization.physical_boundary_jets
    {curve : ℂ→Coupling} {amp : ℂ→ℂ} {b : ℝ}
    (D : UpperNormalization curve amp b) (hb : |b|<1)
    (hK : curve 0∈frontier highDomain) (hp : p (curve 0)^2≠1) :
    ∃V : Set ℂ,IsOpen V ∧ MapsTo (fun t=>D.Z (D.f t)) V highDomain ∧
      (∀ᶠε : ℝ in 𝓝[>] 0,-(ε:ℂ)∈V) ∧ ∀j : ℕ,
      Summable (fun n : ℕ=>‖iteratedDeriv j
        (fun t=>amp t^(2*n+1)*continuedAngularCoefficient (2*n) (curve t)) 0‖) ∧
      Tendsto (fun ε : ℝ=>iteratedDeriv j (fun t=>D.weight (D.f t)*
        ∑'n : ℕ,p (D.Z (D.f t))^n*FormFactors.unscaledFullCoefficient (2*n+1) (D.Z (D.f t)))
          (-(ε:ℂ))/(j.factorial:ℂ)) (𝓝[>] 0) (𝓝 (negativePaperCoefficient curve amp j)) := by
  obtain ⟨r,hr,hrD,hhigh⟩ := D.high_upper_radius hb hK hp
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
  let U : Set ℂ := upperBall r
  let V : Set ℂ := {t | AnalyticAt ℂ D.f t ∧ D.f t∈U}
  have hU : IsOpen U := upperBall_isOpen _
  have hV : IsOpen V := by
    rw [isOpen_iff_mem_nhds]
    intro t ht
    exact ht.1.eventually_analyticAt.and
      (ht.1.continuousAt.tendsto.eventually (hU.mem_nhds ht.2))
  have hsub (u : ℂ) (hu : u∈U) : u∈ball 0 D.radius := ball_subset_ball hrD hu.1
  have hZ : AnalyticOnNhd ℂ D.Z U := fun u hu=>D.Z_analytic u (hsub u hu)
  have hA : AnalyticOnNhd ℂ D.weight U := fun u hu=>D.weight_analytic u (hsub u hu)
  have hS : ∀u∈U,S (D.Z u)≠0 := fun u hu=>D.S_ne u (hsub u hu)
  have hBi : ∀u∈U,0<(negativeChartB D.Z u).im := fun u hu=>D.B_pos u (hsub u hu)
  have he : ∀u∈U,transferC (D.Z u)+transferB (D.Z u)=(b:ℂ)+u := fun u hu=>D.edge u (hsub u hu)
  have hf : AnalyticOnNhd ℂ D.f V := fun _ ht=>ht.1
  have hmap : MapsTo D.f V U := fun _ ht=>ht.2
  have hpath : Tendsto (fun ε : ℝ=>-(ε:ℂ)) (𝓝[>] 0) (𝓝 0) := by
    have h : Continuous (fun ε : ℝ=>-(ε:ℂ)) := Complex.continuous_ofReal.neg
    simpa only [Complex.ofReal_zero,neg_zero] using
      (h.continuousAt (x:=0)).tendsto.mono_left nhdsWithin_le_nhds
  have hfp : Tendsto (fun ε : ℝ=>D.f (-(ε:ℂ))) (𝓝[>] 0) (𝓝 0) := by
    simpa only [D.f_zero,Function.comp_def] using D.f_analytic.continuousAt.tendsto.comp hpath
  have hin : ∀ᶠε : ℝ in 𝓝[>] 0,-(ε:ℂ)∈V := by
    filter_upwards [D.inward,hfp.eventually (ball_mem_nhds (0:ℂ) hr),
      hpath.eventually D.f_analytic.eventually_analyticAt] with ε hi hr' ha
    exact ⟨ha,hr',hi.2⟩
  refine ⟨V,hV,fun t ht=>hhigh _ (hmap ht),hin,?_⟩
  intro j
  obtain ⟨hs,hl⟩ := physical_scaled_high_series_reparametrized_boundary_jets
    hb hB0 hBa hSa hS0 hAa hA0 hZa hS0 hedge hB0 hU hZ hA hhigh hS
      (fun _ _=>rfl) (fun _ _=>rfl) he (fun _ hu=>hu.2) hBi
      (fun u hu=>D.square u (hsub u hu)) (fun u hu=>D.weight_ne u (hsub u hu))
      hV hf D.f_analytic D.f_zero hmap hpath hin j
  have heq (n : ℕ) := (D.coefficient_germ (2*n)).iteratedDeriv_eq j
  constructor
  · simpa only [←heq] using hs
  · simpa only [negativePaperCoefficient,←heq] using hl.div_const (j.factorial:ℂ)

end
end IsingBulk.Joint.Negative
