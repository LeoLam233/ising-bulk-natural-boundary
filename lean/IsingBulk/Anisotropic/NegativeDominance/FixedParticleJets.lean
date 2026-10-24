import IsingBulk.Anisotropic.NegativeDominance.FiniteLowCoefficients
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import IsingBulk.Anisotropic.Final.LocalExtension

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open IsingBulk.First IsingBulk.Anisotropic.RegularEdges Set Filter
open scoped Topology

/-- The actual upper continuation sheet near a regular negative endpoint. -/
def negativePhysicalSheet (lam : ℝ) : Set ℂ :=
  {z | z∉spectralSet lam ∧ spectralS z≠0 ∧
    0<((spectralA lam z+spectralT lam z)/spectralS z).im ∧
    0<(-spectralT lam z/spectralS z).im}

theorem negativePhysicalSheet_isOpen (lam : ℝ) : IsOpen (negativePhysicalSheet lam) := by
  apply isOpen_iff_mem_nhds.mpr
  intro z hz
  have hS : ContinuousAt spectralS z := Complex.continuous_sinh.continuousAt
  have hT : ContinuousAt (spectralT lam) z := by unfold spectralT; fun_prop
  have hA : ContinuousAt (spectralA lam) z := by unfold spectralA; fun_prop
  have he : ContinuousAt (fun w => ((spectralA lam w+spectralT lam w)/spectralS w).im) z :=
    Complex.continuous_im.continuousAt.comp ((hA.add hT).div hS hz.2.1)
  have hB : ContinuousAt (fun w => (-spectralT lam w/spectralS w).im) z :=
    Complex.continuous_im.continuousAt.comp (hT.neg.div hS hz.2.1)
  filter_upwards [(spectralSet_isClosed lam).isOpen_compl.mem_nhds hz.1,
    hS.eventually_ne hz.2.1, he.eventually_const_lt hz.2.2.1,
    hB.eventually_const_lt hz.2.2.2] with w hw hSw hew hBw
  exact ⟨hw,hSw,hew,hBw⟩

theorem continuedAngularCoefficient_eq_unscaled_on_sheet (n : ℕ) (lam : ℝ) :
    EqOn (continuedAngularCoefficient n lam) (unscaledAngularCoefficient n lam)
      (negativePhysicalSheet lam) := by
  intro z hz
  exact continuedAngularCoefficient_eq_unscaled_on_negative_sheet n hz.1 hz.2.1 hz.2.2.1 hz.2.2.2.le

/-- A genuine domain extension, not merely an unrestricted holomorphic germ. -/
theorem fixed_odd_particle_has_domain_extension (n : ℕ) (hN : Odd (n+1))
    {lam b : ℝ} {z : ℂ} (hS : spectralS z≠0)
    (hedge : spectralA lam z+spectralT lam z=(b : ℂ)*spectralS z)
    (hb : |b|<1) (hB : 0<(-spectralT lam z/spectralS z).im) :
    HasDomainExtension (negativePhysicalSheet lam) (unscaledAngularCoefficient n lam) z := by
  have ha := continuedAngularCoefficient_negative_analyticAt n hN hS hedge hb hB
  obtain ⟨U,hU,hUopen,hzU⟩ := mem_nhds_iff.mp ha.eventually_analyticAt
  exact ⟨U,hUopen,hzU,continuedAngularCoefficient n lam,
    fun w hw => hU hw, fun w hw => continuedAngularCoefficient_eq_unscaled_on_sheet n lam hw.2⟩

/-- Every actual fixed odd-particle inward boundary jet exists and is exactly
its analytic continuation coefficient. The unresolved complete odd sum needs
uniform derivative summability, not an additional fixed-index limit. -/
theorem fixed_odd_particle_boundary_jets
    {ι : Type*} {l : Filter ι} {path : ι → ℂ}
    (n : ℕ) (hN : Odd (n+1)) {lam b : ℝ} {z : ℂ}
    (hS : spectralS z≠0) (hedge : spectralA lam z+spectralT lam z=(b : ℂ)*spectralS z)
    (hb : |b|<1) (hB : 0<(-spectralT lam z/spectralS z).im)
    (hp : Tendsto path l (𝓝 z)) (hin : ∀ᶠ t in l, path t∈negativePhysicalSheet lam)
    (j : ℕ) :
    Tendsto (fun t => iteratedDeriv j (unscaledAngularCoefficient n lam) (path t)/(j.factorial : ℂ)) l
      (𝓝 (iteratedDeriv j (continuedAngularCoefficient n lam) z/(j.factorial : ℂ))) := by
  have ha := continuedAngularCoefficient_negative_analyticAt n hN hS hedge hb hB
  have hc : ContinuousAt (iteratedDeriv j (continuedAngularCoefficient n lam)) z := by
    simpa only [iteratedDeriv_eq_iterate] using (ha.iterated_deriv j).continuousAt
  have ht := (hc.tendsto.comp hp).div_const (j.factorial : ℂ)
  apply ht.congr'
  filter_upwards [hin] with t hit
  have he : unscaledAngularCoefficient n lam =ᶠ[𝓝 (path t)] continuedAngularCoefficient n lam := by
    filter_upwards [(negativePhysicalSheet_isOpen lam).mem_nhds hit] with w hw
    exact (continuedAngularCoefficient_eq_unscaled_on_sheet n lam hw).symm
  rw [he.iteratedDeriv_eq]
  rfl

end
end IsingBulk.Anisotropic.NegativeDominance
