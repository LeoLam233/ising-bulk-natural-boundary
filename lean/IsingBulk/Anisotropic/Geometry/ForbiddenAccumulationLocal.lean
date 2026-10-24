import IsingBulk.Anisotropic.Geometry.RegularPrimeDensity
import IsingBulk.Anisotropic.Geometry.CandidateClosure
import IsingBulk.Anisotropic.Final.AnalyticInverse

namespace IsingBulk.Anisotropic
noncomputable section
open Filter Set
open scoped Topology

/-- The actual candidate derivative, rather than an abstract root hypothesis. -/
theorem spectralEquation_hasDerivAt (lam u v : ℝ) (z : ℂ) :
    HasDerivAt (spectralEquation lam (u,v))
      (spectralADeriv lam z-Complex.cosh z*(u:ℂ)-
        ((lam:ℂ)*Complex.cosh ((lam:ℂ)*z))*(v:ℂ)) z :=
  ((spectralA_hasDerivAt lam z).sub ((Complex.hasDerivAt_sinh z).mul_const (u:ℂ))).sub
    ((spectralT_hasDerivAt lam z).mul_const (v:ℂ))

/-- A regular negative U-endpoint gives a genuine simple candidate root. -/
theorem forbidden_candidate_derivative_ne_zero {lam : ℝ} {z : ℂ}
    (hd : spectralDet lam z≠0) (hu : spectralU lam z= -1)
    (hder : deriv (edgeMapU lam (-1)) z≠0) :
    deriv (spectralEquation lam (-1,spectralV lam z)) z≠0 := by
  have ht := spectralT_ne_zero_of_det_ne_zero hd
  have he := edgeMapU_at_endpoint hd hu
  have ha := edgeMapU_analyticAt (e := (-1:ℂ)) ht
  have hprod := (spectralT_hasDerivAt lam z).mul
    (ha.differentiableAt.hasDerivAt.sub_const (spectralV lam z:ℂ))
  have heq : spectralEquation lam (-1,spectralV lam z) =ᶠ[𝓝 z]
      fun w=>spectralT lam w*(edgeMapU lam (-1) w-(spectralV lam z:ℂ)) := by
    filter_upwards [(spectralT_hasDerivAt lam z).continuousAt.eventually_ne ht] with w hw
    unfold spectralEquation edgeMapU
    push_cast
    field_simp
  have hh := hprod.congr_of_eventuallyEq heq
  have hv : edgeMapU lam (-1) z=(spectralV lam z:ℂ) := by simpa using he
  have hresult : deriv (spectralEquation lam (-1,spectralV lam z)) z=
      spectralT lam z*deriv (edgeMapU lam (-1)) z := by
    simpa only [hv,sub_self,mul_zero,zero_add] using hh.deriv
  rw [hresult]
  exact mul_ne_zero ht hder

/-- Keeping V fixed gives the actual transverse local inverse at U=-1.
This constructs candidate roots only; it makes no claim about continuation
of the infinite form-factor sum into the spectral interior. -/
theorem exists_forbidden_candidate_inverse {lam : ℝ} {z : ℂ}
    (hd : spectralDet lam z≠0) (hu : spectralU lam z= -1)
    (hv : |spectralV lam z|<1) (hder : deriv (edgeMapU lam (-1)) z≠0) :
    ∃ψ : ℂ→ℂ,AnalyticAt ℂ ψ (-1) ∧ ψ (-1)=z ∧
      deriv ψ (-1)=spectralS z/deriv (spectralEquation lam (-1,spectralV lam z)) z ∧
      (∀ᶠ w in 𝓝 (-1:ℂ),edgeMapV lam (spectralV lam z:ℂ) (ψ w)=w) ∧
      (∀ᶠ u : ℝ in 𝓝 (-1),
        spectralEquation lam (u,spectralV lam z) (ψ u)=0 ∧
        spectralU lam (ψ u)=u ∧ spectralV lam (ψ u)=spectralV lam z ∧
        (|u|<1 → ψ u∈interior (spectralSet lam))) := by
  have hs := spectralS_ne_zero_of_det_ne_zero hd
  have ha := edgeMapV_analyticAt (lam := lam) (e := (spectralV lam z:ℂ)) hs
  have he : edgeMapV lam (spectralV lam z:ℂ) z= -1 := by
    rw [edgeMapV_at_endpoint hd rfl,hu]
    norm_num
  have hprod := (Complex.hasDerivAt_sinh z).mul
    (ha.differentiableAt.hasDerivAt.add_const 1)
  have heq : spectralEquation lam (-1,spectralV lam z) =ᶠ[𝓝 z]
      fun w=>spectralS w*(edgeMapV lam (spectralV lam z:ℂ) w+1) := by
    filter_upwards [(Complex.hasDerivAt_sinh z).continuousAt.eventually_ne hs] with w hw
    unfold spectralEquation edgeMapV spectralS at *
    push_cast
    field_simp
    ring
  have hrel : deriv (spectralEquation lam (-1,spectralV lam z)) z=
      spectralS z*deriv (edgeMapV lam (spectralV lam z:ℂ)) z := by
    simpa only [he,neg_add_cancel,mul_zero,zero_add,spectralS] using
      (hprod.congr_of_eventuallyEq heq).deriv
  have hg : deriv (edgeMapV lam (spectralV lam z:ℂ)) z≠0 := by
    intro h
    apply forbidden_candidate_derivative_ne_zero hd hu hder
    rw [hrel,h,mul_zero]
  obtain ⟨ψ,hψ,hψ0,hψg,_hgψ⟩ := exists_analytic_local_inverse ha hg
  rw [he] at hψ hψ0 hψg
  have hap : AnalyticAt ℂ (edgeMapV lam (spectralV lam z:ℂ)) (ψ (-1)) := by
    rw [hψ0]
    exact ha
  have heqg : (fun w=>edgeMapV lam (spectralV lam z:ℂ) (ψ w)) =ᶠ[𝓝 (-1:ℂ)]
      (fun w=>w) := hψg
  have hcompose : HasDerivAt
      (fun w=>edgeMapV lam (spectralV lam z:ℂ) (ψ w))
      (deriv (edgeMapV lam (spectralV lam z:ℂ)) z*deriv ψ (-1)) (-1) := by
    simpa only [hψ0,Function.comp_def] using
      (hap.differentiableAt.hasDerivAt.comp (-1) hψ.differentiableAt.hasDerivAt)
  have hidentity : HasDerivAt (fun w : ℂ=>w)
      (deriv (edgeMapV lam (spectralV lam z:ℂ)) z*deriv ψ (-1)) (-1) :=
    hcompose.congr_of_eventuallyEq heqg.symm
  have hmul := hidentity.unique (hasDerivAt_id (-1:ℂ))
  have hψder : deriv ψ (-1)=
      spectralS z/deriv (spectralEquation lam (-1,spectralV lam z)) z := by
    rw [hrel]
    apply (eq_div_iff (mul_ne_zero hs hg)).mpr
    calc
      _ = spectralS z*(deriv (edgeMapV lam (spectralV lam z:ℂ)) z*deriv ψ (-1)) := by ring
      _ = spectralS z := by rw [hmul,mul_one]
  refine ⟨ψ,hψ,hψ0,hψder,hψg,?_⟩
  have hψlim : Tendsto (fun u : ℝ=>ψ (u:ℂ)) (𝓝 (-1)) (𝓝 z) := by
    simpa only [hψ0,Function.comp_def] using hψ.continuousAt.tendsto.comp
      (show Tendsto (fun u : ℝ=>(u:ℂ)) (𝓝 (-1)) (𝓝 (-1:ℂ)) by
        simpa using Complex.continuous_ofReal.continuousAt.tendsto (x := (-1:ℝ)))
  have hcast : Tendsto (fun u : ℝ=>(u:ℂ)) (𝓝 (-1)) (𝓝 (-1:ℂ)) := by
    simpa using Complex.continuous_ofReal.continuousAt.tendsto (x := (-1:ℝ))
  filter_upwards [hcast.eventually hψg,
    hψlim.eventually ((spectralDet_continuous lam).continuousAt.eventually_ne hd)] with u heq hdet
  have hc := coordinates_of_edgeMapV_real hdet heq
  refine ⟨?_,hc.2,hc.1,fun h=>mem_interior_spectralSet_of_strict_coordinates hdet
    (hc.2.symm ▸ h) (hc.1.symm ▸ hv)⟩
  unfold spectralEquation
  rw [spectral_reconstruction hdet,hc.1,hc.2]
  ring

end
end IsingBulk.Anisotropic
