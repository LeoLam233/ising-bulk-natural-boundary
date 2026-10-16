import IsingBulk.Final.LocalExtension
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars

/-! A real C^k extension is weaker than a holomorphic extension. The
obstruction compares actual exterior complex derivatives with the real
Fréchet derivatives of an agreeing extension, rather than assuming that a
smooth extension is holomorphic. -/
namespace IsingBulk.Final
noncomputable section
open Set Filter
open scoped Topology

def HasExteriorCkExtension (f : ℂ → ℂ) (z : ℂ) (k : ℕ) : Prop :=
  ∃ U : Set ℂ, IsOpen U ∧ z ∈ U ∧ ∃ g : ℂ → ℂ,
    ContDiffOn ℝ k g U ∧ EqOn g f (U ∩ {s : ℂ | 1 < ‖s‖})

theorem Ck_extension_of_eventuallyEq_exterior {f g : ℂ → ℂ} {z : ℂ} {k : ℕ}
    (hfg : ∀ᶠ s in 𝓝 z, 1 < ‖s‖ → f s = g s)
    (hg : HasExteriorCkExtension g z k) : HasExteriorCkExtension f z k := by
  obtain ⟨U,hU,hzU,G,hG,hEq⟩ := hg
  obtain ⟨V,hV,hVopen,hzV⟩ := mem_nhds_iff.mp hfg
  refine ⟨U ∩ V,hU.inter hVopen,⟨hzU,hzV⟩,G,hG.mono inter_subset_left,?_⟩
  intro s hs
  exact (hEq ⟨hs.1.1,hs.2⟩).trans (hV hs.1.2 hs.2).symm

theorem no_Ck_extension_of_nonzero_radial_limit {f : ℂ → ℂ} {z L : ℂ}
    (hz : ‖z‖ = 1) (hL : L ≠ 0) (k : ℕ)
    (ha : ∀ᶠ e : ℝ in 𝓝[>] 0, AnalyticAt ℂ f ((1+(e:ℂ))*z))
    (hlim : Tendsto (fun e : ℝ => Real.sqrt e •
        iteratedDeriv k f ((1+(e:ℂ))*z)) (𝓝[>] 0) (𝓝 L)) :
    ¬ HasExteriorCkExtension f z k := by
  rintro ⟨U,hU,hzU,g,hg,heq⟩
  let J : ℂ → ℂ := fun s => iteratedFDeriv ℝ k g s (fun _ => 1)
  have hcont : ContinuousAt J z :=
    (continuous_eval_const (fun _ : Fin k => (1:ℂ))).continuousAt.comp
      ((hg.contDiffAt (hU.mem_nhds hzU)).continuousAt_iteratedFDeriv le_rfl)
  have hpath := radialPath_tendsto z
  have hUevent := hpath.eventually (hU.mem_nhds hzU)
  have hjet : ∀ᶠ e : ℝ in 𝓝[>] 0, iteratedDeriv k f ((1+(e:ℂ))*z) = J ((1+(e:ℂ))*z) := by
    filter_upwards [ha,hUevent,self_mem_nhdsWithin] with e hA heU he
    have hopen : IsOpen (U ∩ {s : ℂ | 1 < ‖s‖}) :=
      hU.inter (isOpen_lt continuous_const continuous_norm)
    have hfg : f =ᶠ[𝓝 ((1+(e:ℂ))*z)] g := by
      filter_upwards [hopen.mem_nhds ⟨heU,radialPath_exterior hz he⟩] with s hs
      exact (heq hs).symm
    have hR : ContDiffAt ℂ k f ((1+(e:ℂ))*z) := hA.contDiffAt
    have hr := hR.restrictScalars_iteratedFDeriv (𝕜 := ℝ)
    have hv := congrArg (fun T : ContinuousMultilinearMap ℝ (fun _ : Fin k => ℂ) ℂ =>
      T (fun _ => 1)) hr
    change iteratedFDeriv ℂ k f ((1+(e:ℂ))*z) (fun _ => 1) =
      iteratedFDeriv ℝ k f ((1+(e:ℂ))*z) (fun _ => 1) at hv
    rw [iteratedDeriv_eq_iteratedFDeriv,hv]
    exact congrArg (fun T : ContinuousMultilinearMap ℝ (fun _ : Fin k => ℂ) ℂ =>
      T (fun _ => 1)) ((hfg.iteratedFDeriv ℝ k).eq_of_nhds)
  have hsqrt : Tendsto Real.sqrt (𝓝[>] (0:ℝ)) (𝓝 0) := by
    simpa using (Real.continuous_sqrt.tendsto (0:ℝ)).mono_left nhdsWithin_le_nhds
  have hzero : Tendsto (fun e : ℝ => Real.sqrt e • J ((1+(e:ℂ))*z))
      (𝓝[>] 0) (𝓝 (0:ℂ)) := by
    simpa using hsqrt.smul (hcont.tendsto.comp hpath)
  have hzF : Tendsto (fun e : ℝ => Real.sqrt e • iteratedDeriv k f ((1+(e:ℂ))*z))
      (𝓝[>] 0) (𝓝 (0:ℂ)) :=
    hzero.congr' (hjet.mono (fun e he => by dsimp only; rw [he]))
  exact hL (tendsto_nhds_unique hlim hzF)

end
end IsingBulk.Final
