import IsingBulk.Joint.FormFactors.ComplexRatioFamilies
import IsingBulk.Joint.Transverse.NegativeLocalSide

namespace IsingBulk.Joint.FormFactors
noncomputable section
open Set Filter Metric
open scoped Topology

/-- A constructed complex-ratio family stays on the actual same physical side
on a smaller closed product polydisk. Every nearby complex-lambda center is
proved to be on the frontier by an actual inward path, not assumed to be so. -/
theorem negative_ratio_raw_common_physical_side {D : Set Coupling} {b : ℝ}
    {amp : Coupling→ℂ} {z₀ lam₀ : ℂ}
    (F : ComplexRatioFamily (Transverse.negativeParameter (b:ℂ)) amp (-1) z₀ lam₀)
    (hD : IsOpen D) (hclosure : (z₀,lam₀*z₀)∈closure D)
    (hDsub : D⊆spectralSetᶜ) (hcomp : ∀a∈D,connectedComponentIn spectralSetᶜ a=D)
    (hp : p (z₀,lam₀*z₀)^2≠1) (hS : S (z₀,lam₀*z₀)≠0)
    (hB : (transferB (z₀,lam₀*z₀)).im<0) (hb : |b|<1) :
    ∃ρ : ℝ,0<ρ ∧ ρ≤F.radius ∧
      (∀u lam : ℂ,‖u‖≤ρ → ‖lam-lam₀‖≤ρ →
        AnalyticAt ℂ F.coupling (u,lam) ∧ S (F.coupling (u,lam))≠0 ∧
        (transferB (F.coupling (u,lam))).im<0 ∧ p (F.coupling (u,lam))^2≠1 ∧
        (F.coupling (u,lam)∈D ↔ 0<u.im)) ∧
      ∀lam : ℂ,‖lam-lam₀‖≤ρ → F.coupling (0,lam)∈frontier D := by
  have h2r : 0≤2*F.radius := by have := F.radius_pos; positivity
  have he0 : Transverse.negativeParameter b (z₀,lam₀*z₀)=0 := by
    rw [←F.coupling_zero]
    exact F.edge_eq 0 lam₀ (by simpa using h2r) (by simpa using h2r)
  obtain ⟨U,hU,hKU,hUf,hside⟩ := Transverse.negativeFace_domain_side
    hclosure hDsub hcomp hS hp (by simpa only [Complex.neg_im,neg_pos] using hB) hb he0
  have hF0 := F.coupling_analytic 0 lam₀ (by simpa using h2r) (by simpa using h2r)
  have hevent : ∀ᶠq : Coupling in 𝓝 (0,lam₀),F.coupling q∈U ∧ p (F.coupling q)^2≠1 := by
    have hmem := hF0.continuousAt.preimage_mem_nhds (by simpa only [F.coupling_zero] using hU.mem_nhds hKU)
    have hpn : ContinuousAt (fun q : Coupling=>p (F.coupling q)^2) (0,lam₀) :=
      (continuous_p.continuousAt.comp hF0.continuousAt).pow 2
    exact inter_mem hmem (hpn.eventually_ne (by simpa only [F.coupling_zero] using hp))
  obtain ⟨R,hR,hball⟩ := Metric.eventually_nhds_iff.mp hevent
  let ρ := min F.radius (R/2)
  have hρ : 0<ρ := lt_min F.radius_pos (half_pos hR)
  have hρF : ρ≤F.radius := min_le_left _ _
  have hρR : ρ<R := (min_le_right _ _).trans_lt (half_lt_self hR)
  have hdata (u lam : ℂ) (hu : ‖u‖≤ρ) (hl : ‖lam-lam₀‖≤ρ) :
      AnalyticAt ℂ F.coupling (u,lam) ∧ S (F.coupling (u,lam))≠0 ∧
      (transferB (F.coupling (u,lam))).im<0 ∧ p (F.coupling (u,lam))^2≠1 ∧
      (F.coupling (u,lam)∈D ↔ 0<u.im) := by
    have huF : ‖u‖≤2*F.radius := hu.trans (by linarith)
    have hlF : ‖lam-lam₀‖≤2*F.radius := hl.trans (by linarith)
    have hh := hball (show dist (u,lam) (0,lam₀)<R from by
      simpa only [Prod.dist_eq,dist_eq_norm,Prod.norm_def,Prod.fst_sub,Prod.snd_sub,sub_zero,max_lt_iff] using
        And.intro (hu.trans_lt hρR) (hl.trans_lt hρR))
    have hf := hUf hh.1
    exact ⟨F.coupling_analytic u lam huF hlF,hf.1,(by simpa only [Complex.neg_im,neg_pos] using hf.2.1),hh.2,
      by simpa only [F.edge_eq u lam huF hlF] using hside _ hh.1⟩
  refine ⟨ρ,hρ,hρF,hdata,?_⟩
  intro lam hlam
  have hcenter := hdata 0 lam (by simpa using hρ.le) hlam
  have hpath : ContinuousAt (fun t : ℝ => F.coupling ((t:ℂ)*Complex.I,lam)) 0 := by
    have hc : ContinuousAt F.coupling ((0:ℂ)*Complex.I,lam) := by simpa using hcenter.1.continuousAt
    exact hc.comp (f:=fun t : ℝ => ((t:ℂ)*Complex.I,lam)) (by fun_prop)
  have hlim : Tendsto (fun t : ℝ => F.coupling ((t:ℂ)*Complex.I,lam)) (𝓝[>] 0)
      (𝓝 (F.coupling (0,lam))) := by
    simpa using hpath.tendsto.mono_left nhdsWithin_le_nhds
  have hmem : ∀ᶠt : ℝ in 𝓝[>] 0,F.coupling ((t:ℂ)*Complex.I,lam)∈D := by
    filter_upwards [Ioo_mem_nhdsGT hρ] with t ht
    apply (hdata _ lam (by simpa [abs_of_pos ht.1] using ht.2.le) hlam).2.2.2.2.mpr
    simpa using ht.1
  rw [hD.frontier_eq]
  refine ⟨mem_closure_of_tendsto hlim hmem,?_⟩
  intro hd
  have hh := hcenter.2.2.2.2.mp hd
  simp at hh

theorem negative_ratio_raw_common_high_side {b : ℝ} {amp : Coupling→ℂ} {z₀ lam₀ : ℂ}
    (F : ComplexRatioFamily (Transverse.negativeParameter (b:ℂ)) amp (-1) z₀ lam₀)
    (hK : (z₀,lam₀*z₀)∈closure highDomain) (hp : p (z₀,lam₀*z₀)^2≠1)
    (hS : S (z₀,lam₀*z₀)≠0) (hB : (transferB (z₀,lam₀*z₀)).im<0) (hb : |b|<1) :
    ∃ρ : ℝ,0<ρ ∧ ρ≤F.radius ∧
      (∀u lam : ℂ,‖u‖≤ρ → ‖lam-lam₀‖≤ρ →
        AnalyticAt ℂ F.coupling (u,lam) ∧ S (F.coupling (u,lam))≠0 ∧
        (transferB (F.coupling (u,lam))).im<0 ∧ p (F.coupling (u,lam))^2≠1 ∧
        (F.coupling (u,lam)∈highDomain ↔ 0<u.im)) ∧
      ∀lam : ℂ,‖lam-lam₀‖≤ρ → F.coupling (0,lam)∈frontier highDomain :=
  negative_ratio_raw_common_physical_side F highDomain_isOpen hK highDomain_subset_spectralComplement
    highDomain_component hp hS hB hb

theorem negative_ratio_raw_common_low_side {b : ℝ} {amp : Coupling→ℂ} {z₀ lam₀ : ℂ}
    (F : ComplexRatioFamily (Transverse.negativeParameter (b:ℂ)) amp (-1) z₀ lam₀)
    (hK : (z₀,lam₀*z₀)∈closure lowDomain) (hp : p (z₀,lam₀*z₀)^2≠1)
    (hS : S (z₀,lam₀*z₀)≠0) (hB : (transferB (z₀,lam₀*z₀)).im<0) (hb : |b|<1) :
    ∃ρ : ℝ,0<ρ ∧ ρ≤F.radius ∧
      (∀u lam : ℂ,‖u‖≤ρ → ‖lam-lam₀‖≤ρ →
        AnalyticAt ℂ F.coupling (u,lam) ∧ S (F.coupling (u,lam))≠0 ∧
        (transferB (F.coupling (u,lam))).im<0 ∧ p (F.coupling (u,lam))^2≠1 ∧
        (F.coupling (u,lam)∈lowDomain ↔ 0<u.im)) ∧
      ∀lam : ℂ,‖lam-lam₀‖≤ρ → F.coupling (0,lam)∈frontier lowDomain :=
  negative_ratio_raw_common_physical_side F lowDomain_isOpen hK lowDomain_subset_spectralComplement
    lowDomain_component hp hS hB hb

end
end IsingBulk.Joint.FormFactors
