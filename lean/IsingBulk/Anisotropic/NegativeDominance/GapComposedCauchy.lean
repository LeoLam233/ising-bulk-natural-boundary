import IsingBulk.Anisotropic.NegativeDominance.GapComposedControl

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open IsingBulk.Anisotropic.RegularEdges Set Metric

/-- Actual complete-density Cauchy jets on the paper-coordinate a/N disk.
The constants precede every order j, particle N and angular configuration. -/
theorem composed_fullIntegrand_cauchy_of_boundary_gap {b : ℝ} {B S f : ℂ→ℂ}
    (hb : |b|<1) (hB : 0<(B 0).im) (hBa : AnalyticAt ℂ B 0)
    (hSa : AnalyticAt ℂ S 0) (hS0 : S 0≠0) (hf : AnalyticAt ℂ f 0) (hf0 : f 0=0)
    (κ : ℝ) (hκ : 0<κ) :
    ∃a r C M K : ℝ,0<a ∧ 0<r ∧ r<1 ∧ 0<C ∧ 0<M ∧ 0<K ∧
      ∀N : ℕ,1≤N → ∀q : Fin N→ℝ,(∀i,q i∈Icc (-Real.pi) Real.pi) →
      κ≤‖1-edgeRootProduct b B 0 q‖ → ∀j : ℕ,∀u : ℂ,‖u‖<a/(N : ℝ) →
      ‖iteratedDeriv j (fun w=>edgeFullIntegrand b B S (f w) q) u‖≤
        (j.factorial : ℝ)*(K*particleEdgeMajorant r C M N)/(a/(N : ℝ))^j := by
  obtain ⟨a,r,C,M,K,ha,hr,hr1,hC,hM,hK,hcontrol⟩ :=
    composed_fullIntegrand_disk_of_boundary_gap hb hB hBa hSa hS0 hf hf0 κ hκ
  refine ⟨a/3,r,C,M,K,by positivity,hr,hr1,hC,hM,hK,?_⟩
  intro N hN q hq hgap j u hu
  have hNp : (0 : ℝ)<N := by exact_mod_cast (by omega : 0<N)
  let R : ℝ := (a/3)/(N : ℝ)
  have hR : 0<R := by dsimp [R]; positivity
  have hbig : a/(N : ℝ)=3*R := by dsimp [R]; ring
  have hsub : closedBall u R⊆ball 0 (a/(N : ℝ)) := by
    intro w hw
    have hwu : ‖w-u‖≤R := by simpa only [mem_closedBall,dist_eq_norm] using hw
    have htri := norm_add_le (w-u) u
    rw [sub_add_cancel] at htri
    change dist w 0<a/(N : ℝ)
    rw [dist_zero_right,hbig]
    change ‖u‖<R at hu
    linarith
  apply Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le j hR
  · apply DifferentiableOn.diffContOnCl_ball (U := ball 0 (a/(N : ℝ))) _ hsub
    intro w hw
    exact (hcontrol N hN q hq hgap w (by simpa only [mem_ball,dist_zero_right] using hw)).1.differentiableAt.differentiableWithinAt
  · intro w hw
    exact (hcontrol N hN q hq hgap w
      (by simpa only [mem_ball,dist_zero_right] using hsub (sphere_subset_closedBall hw))).2

end
end IsingBulk.Anisotropic.NegativeDominance
