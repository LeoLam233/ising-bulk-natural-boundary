import IsingBulk.Anisotropic.Geometry.DomainNonvanishing
import IsingBulk.Anisotropic.Geometry.PuncturedTopology

namespace IsingBulk.Anisotropic
noncomputable section
open scoped Topology
open Set Filter Metric

theorem omegaH_spectralS_ne_zero {lam : ℝ} (hlam : 0<lam) {z : ℂ}
    (hz : z∈omegaH lam) (hz0 : z≠0) : spectralS z≠0 := by
  intro hs
  have hb := abs_lt.mp (central_strip_bounds hlam hz.1).1
  have h := norm_sinh_sq z
  change Complex.sinh z=0 at hs
  rw [hs,norm_zero,zero_pow (by decide : 2≠0)] at h
  have hx : z.re=0 := Real.sinh_eq_zero.mp (by nlinarith [sq_nonneg (Real.sin z.im)])
  have hy : Real.sin z.im=0 := by nlinarith [sq_nonneg (Real.sinh z.re)]
  have hy0 : z.im=0 := (Real.sin_eq_zero_iff_of_lt_of_lt
    (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])).mp hy
  apply hz0
  exact Complex.ext (by simpa using hx) (by simpa using hy0)


/-- Removing the star center from an open complex star-convex domain preserves connectedness. -/
theorem open_starConvex_punctured_isPreconnected {s : Set ℂ} (hs : IsOpen s)
    (h0 : (0:ℂ)∈s) (hstar : StarConvex ℝ (0:ℂ) s) : IsPreconnected (s\{0}) := by
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (hs.mem_nhds h0)
  let B : Set ℂ := ball 0 r\{0}
  have hB : IsPreconnected B := complex_punctured_ball_isPreconnected 0 hr
  have hBs : B⊆s\{0} := fun _ hz => ⟨hball hz.1,hz.2⟩
  have hb : ((r/2:ℝ):ℂ)∈B := by
    constructor
    · change dist ((r/2:ℝ):ℂ) 0<r
      simp only [dist_zero_right,Complex.norm_real,Real.norm_eq_abs]
      rw [abs_of_pos (by positivity : 0<r/2)]
      linarith
    · change ((r/2:ℝ):ℂ)≠0
      exact_mod_cast (by positivity : r/2≠0)
  let C := connectedComponentIn (s\{0}) ((r/2:ℝ):ℂ)
  have hBC : B⊆C := hB.subset_connectedComponentIn hb hBs
  have hCs : C⊆s\{0} := connectedComponentIn_subset _ _
  have hsC : s\{0}⊆C := by
    intro x hx
    let g : ℝ→ℂ := fun t => t • x
    let R : Set ℂ := g '' Ioc (0:ℝ) 1
    have hg : Continuous g := by fun_prop
    have hR : IsPreconnected R := isPreconnected_Ioc.image g hg.continuousOn
    have hRs : R⊆s\{0} := by
      rintro w ⟨t,ht,rfl⟩
      refine ⟨hstar.smul_mem hx.1 ht.1.le ht.2,?_⟩
      change t • x≠0
      exact smul_ne_zero ht.1.ne' hx.2
    have hgb : ∀ᶠ t in 𝓝 (0:ℝ), g t∈ball 0 r :=
      hg.continuousAt.preimage_mem_nhds (by simpa [g] using ball_mem_nhds (0:ℂ) hr)
    have htone : ∀ᶠ t in 𝓝 (0:ℝ), t<1 :=
      continuousAt_id.eventually_lt_const (by norm_num : (0:ℝ)<1)
    have hex : ∀ᶠ t in 𝓝[>] (0:ℝ), t∈Ioc (0:ℝ) 1 ∧ g t∈ball 0 r := by
      filter_upwards [hgb.filter_mono nhdsWithin_le_nhds,htone.filter_mono nhdsWithin_le_nhds,
        self_mem_nhdsWithin] with t ht ht1 ht0
      exact ⟨⟨ht0,ht1.le⟩,ht⟩
    obtain ⟨t,ht,htball⟩ := hex.exists
    have htR : g t∈R := ⟨t,ht,rfl⟩
    have htB : g t∈B := ⟨htball,(hRs htR).2⟩
    have hRC : R⊆C := by
      have hc := hR.subset_connectedComponentIn htR hRs
      rw [←connectedComponentIn_eq (hBC htB)] at hc
      exact hc
    apply hRC
    exact ⟨1,⟨by norm_num,le_rfl⟩,by simp [g]⟩
  have heq : s\{0}=C := Subset.antisymm hsC hCs
  rw [heq]
  exact isPreconnected_connectedComponentIn

theorem omegaH_punctured_isPreconnected {lam : ℝ} (hlam : 0<lam) :
    IsPreconnected (omegaH lam\{0}) :=
  open_starConvex_punctured_isPreconnected (omegaH_isOpen hlam) (zero_mem_omegaH hlam) (omegaH_starConvex hlam)

end
end IsingBulk.Anisotropic
