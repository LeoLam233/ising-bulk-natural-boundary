import IsingBulk.Preferred22.ShellCover

/-! The genuine actual shell cover also supplies global strong
measurability; a finite nonnegative integral therefore yields ordinary
Bochner integrability, without assuming it on the full region. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology ENNReal

theorem preferredRightRegion_integrable_of_shells {n : ℕ} (hn : 0<n)
    (d : PreferredBranchData) (B : PreferredCoareaBump d) {δB : ℝ} (hδB : δB<B.delta)
    {E : Type*} [NormedAddCommGroup E] (f : (Fin n → ℝ) → E)
    (hi : ∀ m : ℕ,∀ l : {l : ℤ // l∈preferredMeanIndices (n+1)},∀ i a : Fin (n+1),
      IntegrableOn f (preferredRightShell d B δB (preferredDyadicRadius m) l.1 i a))
    (hb : (∫⁻ θ in preferredRightRegion d B δB,ENNReal.ofReal ‖f θ‖)<∞) :
    IntegrableOn f (preferredRightRegion d B δB) := by
  have hA : AEStronglyMeasurable f (volume.restrict
      (⋃ m : ℕ, ⋃ l : {l : ℤ // l∈preferredMeanIndices (n+1)},
        ⋃ i : Fin (n+1), ⋃ a : Fin (n+1),
          preferredRightShell d B δB (preferredDyadicRadius m) l.1 i a)) :=
    AEStronglyMeasurable.iUnion (fun m => AEStronglyMeasurable.iUnion (fun l =>
      AEStronglyMeasurable.iUnion (fun i => AEStronglyMeasurable.iUnion (fun a => (hi m l i a).1))))
  have hAd := hA.mono_set (preferredRightRegion_shell_cover d B hδB)
  have hAe : AEStronglyMeasurable f (volume.restrict (preferredRightRegion d B δB)) := by
    rw [← Measure.restrict_congr_set (sdiff_null_ae_eq_self (preferredRightCollision_null hn d B hδB))]
    exact hAd
  exact ⟨hAe,(hasFiniteIntegral_iff_norm f).mpr hb⟩

end
end IsingBulk.Preferred22
