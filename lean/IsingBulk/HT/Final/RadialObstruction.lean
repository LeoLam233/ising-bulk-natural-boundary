import IsingBulk.Final.AnalyticFactorTransfer
import IsingBulk.HT.Final.PhysicalNormalization

/-! HT inverse-epsilon obstruction. The LT endpoint uses a square-root scale,
so its limit theorem cannot be specialized to this exponent. We reuse its
actual extension predicate, radial path geometry, and analytic-factor transfer.
The statements here are general analytic support lemmas, not HT FIRST or TAIL. -/
namespace IsingBulk.HT.Final
noncomputable section
open Filter Set IsingBulk.Final
open scoped Topology

/-- Any scale tending to zero makes an analytic boundary derivative vanish.
Consequently a nonzero scaled radial limit forbids a genuine extension. -/
theorem no_extension_of_nonzero_scaled_radial_limit
    {f : ℂ → ℂ} {z L : ℂ} {a : ℝ → ℝ}
    (hz : ‖z‖=1) (hL : L ≠ 0) (k : ℕ)
    (ha : Tendsto a (𝓝[>] 0) (𝓝 0))
    (hlim : Tendsto (fun e : ℝ => a e •
      iteratedDeriv k f ((1+(e:ℂ))*z)) (𝓝[>] 0) (𝓝 L)) :
    ¬ HasExteriorExtension f z := by
  rintro ⟨U,hU,hzU,g,hg,hEq⟩
  have hp := radialPath_tendsto z
  have hderiv : ∀ᶠ e : ℝ in 𝓝[>] 0,
      iteratedDeriv k f ((1+(e:ℂ))*z) = iteratedDeriv k g ((1+(e:ℂ))*z) := by
    filter_upwards [hp.eventually (hU.mem_nhds hzU),self_mem_nhdsWithin] with e heU he
    apply Filter.EventuallyEq.iteratedDeriv_eq
    have hopen : IsOpen (U ∩ {s : ℂ | 1 < ‖s‖}) :=
      hU.inter (isOpen_lt continuous_const continuous_norm)
    filter_upwards [hopen.mem_nhds ⟨heU,radialPath_exterior hz he⟩] with s hs
    exact (hEq hs).symm
  have hc : ContinuousAt (iteratedDeriv k g) z := by
    simpa only [iteratedDeriv_eq_iterate] using ((hg z hzU).iterated_deriv k).continuousAt
  have hzero : Tendsto (fun e : ℝ => a e •
      iteratedDeriv k g ((1+(e:ℂ))*z)) (𝓝[>] 0) (𝓝 (0:ℂ)) := by
    simpa only [zero_smul,Function.comp_def] using ha.smul (hc.tendsto.comp hp)
  have hfzero : Tendsto (fun e : ℝ => a e •
      iteratedDeriv k f ((1+(e:ℂ))*z)) (𝓝[>] 0) (𝓝 (0:ℂ)) :=
    hzero.congr' (hderiv.mono (fun e he => by dsimp only; rw [he]))
  exact hL (tendsto_nhds_unique hlim hfzero)

theorem epsilon_limit_of_isLittleO {F : ℝ → ℂ} {L : ℂ}
    (h : Asymptotics.IsLittleO (𝓝[>] (0:ℝ))
      (fun e => F e-(e:ℂ)⁻¹*L) (fun e => (e:ℂ)⁻¹)) :
    Tendsto (fun e : ℝ => e • F e) (𝓝[>] 0) (𝓝 L) := by
  have ht := h.tendsto_div_nhds_zero.add_const L
  simp only [zero_add] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with e he
  have hn : (e:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr he.ne'
  simp only [Complex.real_smul]
  field_simp
  ring

/-- The HT leading inverse-distance scale is epsilon, not sqrt(epsilon). -/
theorem no_extension_of_nonzero_epsilon_radial_limit {f : ℂ → ℂ} {z L : ℂ}
    (hz : ‖z‖=1) (hL : L ≠ 0) (k : ℕ)
    (hlim : Tendsto (fun e : ℝ => e •
      iteratedDeriv k f ((1+(e:ℂ))*z)) (𝓝[>] 0) (𝓝 L)) :
    ¬ HasExteriorExtension f z :=
  no_extension_of_nonzero_scaled_radial_limit hz hL k
    (tendsto_id.mono_left nhdsWithin_le_nhds) hlim

/-- Physical-prefactor transfer uses the established nonzero analytic-factor
lemma. It does not assume or prove that the abstract f is the HT bulk sum. -/
theorem no_extension_after_ht_prefactor {f : ℂ → ℂ} {z : ℂ}
    (hz : ‖z‖=1) (hfour : z^4 ≠ 1)
    (hf : ¬ HasExteriorExtension f z) :
    ¬ HasExteriorExtension (fun t => exteriorPrefactor t*f t) z := by
  obtain ⟨ha,hn⟩ := exteriorPrefactor_regular_at_unit_nonaxis hz hfour
  exact no_extension_mul_analytic_factor ha hn hf

end
end IsingBulk.HT.Final
