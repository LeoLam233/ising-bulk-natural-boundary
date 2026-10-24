import IsingBulk.Anisotropic.RegularEdges.LeadingMultiplier
import IsingBulk.Anisotropic.Final.LocalExtension

namespace IsingBulk.Anisotropic.RegularEdges
noncomputable section
open IsingBulk.First Set Filter
open scoped Topology

/-- A nonzero scaled actual derivative limit rules out every local analytic extension
from the open side. The comparison uses equality of genuine derivatives on that side. -/
theorem no_domain_extension_of_scaled_jet_limit {U : Set ℂ} {F : ℂ→ℂ} {a k : ℕ} {C : ℂ}
    (hU : IsOpen U) (ha : 0<a) (hC : C≠0)
    (hin : ∀ᶠ t : ℝ in 𝓝[>] 0,Complex.I*(t:ℂ)^2∈U)
    (hlim : Tendsto (fun t : ℝ => (t^a) • iteratedDeriv k F (Complex.I*(t:ℂ)^2))
      (𝓝[>] 0) (𝓝 C)) : ¬HasDomainExtension U F 0 := by
  rintro ⟨V,hV,h0V,g,hg,heq⟩
  have htend : Tendsto (fun t : ℝ => Complex.I*(t:ℂ)^2) (𝓝[>] 0) (𝓝 0) := by
    simpa using! ((by fun_prop : Continuous (fun t : ℝ => Complex.I*(t:ℂ)^2)).tendsto 0).mono_left nhdsWithin_le_nhds
  have hj := (analyticAt_iteratedDeriv (hg 0 h0V) k).continuousAt.tendsto.comp htend
  have hp : Tendsto (fun t : ℝ => t^a) (𝓝[>] 0) (𝓝 0) := by
    simpa [zero_pow (Nat.ne_of_gt ha)] using
      ((tendsto_id : Tendsto (fun t : ℝ => t) (𝓝 0) (𝓝 0)).pow a).mono_left nhdsWithin_le_nhds
  have hz : Tendsto (fun t : ℝ => (t^a) • iteratedDeriv k g (Complex.I*(t:ℂ)^2))
      (𝓝[>] 0) (𝓝 0) := by simpa only [zero_smul,Function.comp_apply] using! hp.smul hj
  have hfz : Tendsto (fun t : ℝ => (t^a) • iteratedDeriv k F (Complex.I*(t:ℂ)^2))
      (𝓝[>] 0) (𝓝 0) := by
    apply hz.congr'
    filter_upwards [hin,htend.eventually (hV.mem_nhds h0V)] with t htU htV
    have he : g=ᶠ[𝓝 (Complex.I*(t:ℂ)^2)] F := by
      filter_upwards [(hV.inter hU).mem_nhds ⟨htV,htU⟩] with u hu
      exact heq hu
    rw [he.iteratedDeriv_eq k]
  exact hC (tendsto_nhds_unique hlim hfz)

end
end IsingBulk.Anisotropic.RegularEdges
