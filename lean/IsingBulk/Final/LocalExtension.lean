import IsingBulk.Final.RadialNoncancellation
import IsingBulk.First.ExteriorAnalyticGeometry
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-! Local holomorphic extension is expressed by agreement on the actual open
exterior overlap. The obstruction uses a proved radial derivative limit. -/
namespace IsingBulk.Final
noncomputable section
open Filter Set
open scoped Topology

/-- A genuine local extension across a point, with an open overlap on which
all derivatives agree. No global continuation is hidden in this definition. -/
def HasExteriorExtension (f : ℂ → ℂ) (z : ℂ) : Prop :=
  ∃ U : Set ℂ, IsOpen U ∧ z ∈ U ∧ ∃ g : ℂ → ℂ,
    AnalyticOnNhd ℂ g U ∧ EqOn g f (U ∩ {s : ℂ | 1 < ‖s‖})

theorem radialPath_tendsto (z : ℂ) :
    Tendsto (fun e : ℝ => (1+(e:ℂ))*z) (𝓝[>] 0) (𝓝 z) := by
  have h : Tendsto (fun e : ℝ => (e:ℂ)) (𝓝[>] 0) (𝓝 0) := by
    simpa using (Complex.continuous_ofReal.tendsto (0:ℝ)).mono_left nhdsWithin_le_nhds
  simpa using ((tendsto_const_nhds (x := (1:ℂ))).add h).mul_const z

theorem radialPath_exterior {z : ℂ} (hz : ‖z‖ = 1) {e : ℝ} (he : 0 < e) :
    1 < ‖(1+(e:ℂ))*z‖ := by
  rw [norm_mul, hz, mul_one]
  have h : 1+(e:ℂ) = ((1+e:ℝ):ℂ) := by simp
  rw [h, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  linarith

/-- Any nonzero normalized radial derivative limit forbids local extension.
The derivative is the complex derivative of the actual exterior function. -/
theorem no_extension_of_nonzero_radial_limit {f : ℂ → ℂ} {z L : ℂ}
    (hz : ‖z‖ = 1) (hL : L ≠ 0) (k : ℕ)
    (hlim : Tendsto (fun e : ℝ => Real.sqrt e •
        iteratedDeriv k f ((1+(e:ℂ))*z)) (𝓝[>] 0) (𝓝 L)) :
    ¬ HasExteriorExtension f z := by
  rintro ⟨U,hU,hzU,g,hg,heq⟩
  have hpath := radialPath_tendsto z
  have hUevent := hpath.eventually (hU.mem_nhds hzU)
  have hderiv : ∀ᶠ e : ℝ in 𝓝[>] 0,
      iteratedDeriv k f ((1+(e:ℂ))*z) = iteratedDeriv k g ((1+(e:ℂ))*z) := by
    filter_upwards [hUevent,self_mem_nhdsWithin] with e heU he
    apply Filter.EventuallyEq.iteratedDeriv_eq
    have hopen : IsOpen (U ∩ {s : ℂ | 1 < ‖s‖}) :=
      hU.inter (isOpen_lt continuous_const continuous_norm)
    filter_upwards [hopen.mem_nhds ⟨heU,radialPath_exterior hz he⟩] with s hs
    exact (heq hs).symm
  have hcont : ContinuousAt (iteratedDeriv k g) z := by
    simpa only [iteratedDeriv_eq_iterate] using ((hg z hzU).iterated_deriv k).continuousAt
  have hgpath := hcont.tendsto.comp hpath
  have hsqrt : Tendsto Real.sqrt (𝓝[>] (0:ℝ)) (𝓝 0) := by
    simpa only [Real.sqrt_zero] using
      (Real.continuous_sqrt.tendsto (0:ℝ)).mono_left nhdsWithin_le_nhds
  have hzero : Tendsto (fun e : ℝ => Real.sqrt e •
      iteratedDeriv k g ((1+(e:ℂ))*z)) (𝓝[>] 0) (𝓝 (0:ℂ)) := by
    simpa using hsqrt.smul hgpath
  have hzeroF : Tendsto (fun e : ℝ => Real.sqrt e •
      iteratedDeriv k f ((1+(e:ℂ))*z)) (𝓝[>] 0) (𝓝 (0:ℂ)) :=
    hzero.congr' (hderiv.mono (fun e he => by dsimp only; rw [he]))
  exact hL (tendsto_nhds_unique hlim hzeroF)

/-- Obstructions on a dense boundary subset rule out extension at every point
of its closure, including the axis points absent from the selected family. -/
theorem no_extension_on_closure {f : ℂ → ℂ} {S : Set ℂ}
    (hS : ∀ z ∈ S, ¬ HasExteriorExtension f z) {z : ℂ} (hz : z ∈ closure S) :
    ¬ HasExteriorExtension f z := by
  rintro ⟨U,hU,hzU,g,hg,heq⟩
  obtain ⟨w,hwU,hwS⟩ := mem_closure_iff.mp hz U hU hzU
  exact hS w hwS ⟨U,hU,hwU,g,hg,heq⟩

/-- Equality of actual exterior germs near the boundary transfers extensions.
The equality is only required on the exterior part of that neighborhood. -/
theorem extension_of_eventuallyEq_exterior {f g : ℂ → ℂ} {z : ℂ}
    (hfg : ∀ᶠ s in 𝓝 z, 1 < ‖s‖ → f s = g s)
    (hg : HasExteriorExtension g z) : HasExteriorExtension f z := by
  obtain ⟨U,hU,hzU,G,hG,hEq⟩ := hg
  obtain ⟨V,hV,hVopen,hzV⟩ := mem_nhds_iff.mp hfg
  refine ⟨U ∩ V,hU.inter hVopen,⟨hzU,hzV⟩,G,hG.mono inter_subset_left,?_⟩
  intro s hs
  exact (hEq ⟨hs.1.1,hs.2⟩).trans (hV hs.1.2 hs.2).symm

theorem no_extension_of_eventuallyEq_exterior {f g : ℂ → ℂ} {z : ℂ}
    (hfg : ∀ᶠ s in 𝓝 z, 1 < ‖s‖ → f s = g s)
    (hf : ¬ HasExteriorExtension f z) : ¬ HasExteriorExtension g z :=
  fun hg => hf (extension_of_eventuallyEq_exterior hfg hg)

end
end IsingBulk.Final
