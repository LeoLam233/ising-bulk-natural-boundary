import IsingBulk.Anisotropic.NegativeCycles.ShiftedInnerPole

namespace IsingBulk.Joint.Negative
noncomputable section
open IsingBulk.First IsingBulk.Anisotropic.NegativeNormalForm IsingBulk.Anisotropic.NegativeCycles Set Filter MeasureTheory Metric
open scoped Topology BigOperators
set_option maxHeartbeats 1500000

theorem universal_shifted_pole_properties (phi : ℝ) (hphi : Real.sin phi≠0)
    (r C a : ℝ) (hr : 0<r) (ha : 0<a) :
    ∃ ρ : ℝ, 0<ρ ∧ ∀ B : ℂ → ℂ, ∀ n : ℕ, ∀ d : ℂ, ‖d‖<ρ →
      ∀ P : UniformProjectedWitness B phi hphi n d r C,
      ∀ v : Config n, ‖v‖<ρ →
        AnalyticAt ℂ (shiftedInnerPole d P.T) v ∧
        ‖shiftedInnerPole d P.T v‖≤a/2 ∧
        poleEquation B phi hphi 0 (shiftedInnerPole d P.T v) v=0 := by
  have ht : Tendsto (fun d : ℂ => 1-Complex.cos d) (𝓝 0) (𝓝 0) := by
    have hh : ContinuousAt (fun d : ℂ => 1-Complex.cos d) 0 := by fun_prop
    simpa using hh.tendsto
  have hb : ∀ᶠ z : ℂ in 𝓝 0, ‖z‖<a/4 := by
    have hb' : ∀ᶠ z : ℂ in 𝓝 0, z∈ball 0 (a/4) :=
      Metric.ball_mem_nhds (0:ℂ) (show 0<a/4 by positivity)
    filter_upwards [hb'] with z hz
    simpa using hz
  obtain ⟨δ,hδ,hδbound⟩ := Metric.eventually_nhds_iff.mp (ht.eventually hb)
  let ρ := min δ (min (r/2) (a/16))
  have hρ : 0<ρ := lt_min hδ (lt_min (by positivity) (by positivity))
  have hρδ : ρ≤δ := min_le_left _ _
  have hρr : ρ≤r/2 := (min_le_right _ _).trans (min_le_left _ _)
  have hρa : ρ≤a/16 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨ρ,hρ,?_⟩
  intro B n d hd P v hv
  have hshift : ‖(fun i => v i-d : Config n)‖<2*ρ := by
    apply (pi_norm_le_iff_of_nonneg (by positivity : 0≤‖v‖+‖d‖)).mpr
      (fun i => (norm_sub_le (v i) d).trans (add_le_add (norm_le_pi_norm v i) le_rfl)) |>.trans_lt
    linarith
  have hsr : ‖(fun i => v i-d : Config n)‖<2*r := by linarith
  have htau : ‖1-Complex.cos d‖<a/4 := hδbound (by simpa [dist_zero_right] using hd.trans_le hρδ)
  have hT := P.t_analytic (fun i => v i-d) (by simpa using hsr)
  have hmap : AnalyticAt ℂ (fun w : Config n => fun i => w i-d) v := by
    exact analyticAt_id.sub analyticAt_const
  refine ⟨hT.fun_comp_of_eq (f := fun w : Config n => fun i => w i-d) hmap rfl,?_,?_⟩
  · have hLip := P.t_lip (fun i => v i-d) 0 hsr (by simpa using (show 0<2*r by positivity))
    rw [P.t_zero,sub_zero] at hLip
    have hh := norm_add_le (P.T (fun i => v i-d)-(1-Complex.cos d)) (1-Complex.cos d)
    rw [sub_add_cancel] at hh
    change ‖P.T (fun i => v i-d)‖≤a/2
    linarith
  · rw [poleEquation_shift]
    exact (P.t_pole (fun i => v i-d) hsr).1


end
end IsingBulk.Joint.Negative
