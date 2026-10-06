import IsingBulk.First.OnsiteInactiveNeighborhood
import IsingBulk.First.OnsiteSeparation
import IsingBulk.First.ComplementActiveChart
import IsingBulk.First.ComplementSimplex

/-! The selected source geometry produces a genuine fixed angular chart with
simultaneous inactive-factor regularity and active-factor separation. -/
namespace IsingBulk.First
noncomputable section
open Filter
open scoped Topology ContDiff

/-- At every unit configuration, one radius and one direction
work for the literal absolute-angle source factors on a fixed neighborhood.
Both the angular chart and direction are chosen before s or auxiliary values. -/
theorem onsite_active_chart {N : ℕ} (S : ℝ) (hlevel : 0 < S ∧ S < 2)
    (s₀ : ℂ) (hs₀ : s₀ ≠ 0)
    (hS : sourceS s₀ = (S : ℂ))
    (u₀ : DoubleAngularVector N)
    (J : Finset (SingularFactorIndex N))
    (hJ : ∀ f, f ∈ J ↔ isOnsiteFactor f ∧ singularFactorActive (angleTuple 1 u₀.1) (angleTuple 1 u₀.2)
      S f) :
    ∃ (e : DoubleAngularVector N) (δ ρ : ℝ), 0 < δ ∧ 0 < ρ ∧
      ∀ (r : ℝ) (s : ℂ) (u : DoubleAngularVector N),
      dist ((r,s),u) ((1,s₀),u₀) < ρ →
      ((r,s),u) ∈ onsiteInactiveDomain J ∧
      ∀ f ∈ J, δ ≤ angularDot e (dampedSingularVector r
        (torusShift (fun _ => 1) u.1) (torusShift (fun _ => 1) u.2) f) := by
  have hx (i) : ‖angleTuple 1 u₀.1 i‖ = 1 := anglePoint_norm (by norm_num) _
  have hy (i) : ‖angleTuple 1 u₀.2 i‖ = 1 := anglePoint_norm (by norm_num) _
  obtain ⟨e,δ,hδ,hsep⟩ := onsite_active_uniform_separator hx hy hlevel
  let F : (ℝ × ℂ) × DoubleAngularVector N → ℝ × (Fin N → ℂ) × (Fin N → ℂ) :=
    fun q => (q.1.1,angleTuple 1 q.2.1,angleTuple 1 q.2.2)
  have hF : Continuous F := by
    exact continuous_fst.fst.prodMk
      (((angleTuple_continuous 1).comp continuous_snd.fst).prodMk
        ((angleTuple_continuous 1).comp continuous_snd.snd))
  have he : ∀ᶠ q : (ℝ × ℂ) × DoubleAngularVector N in 𝓝 ((1,s₀),u₀),
      ∀ f ∈ J, δ ≤ angularDot e (dampedSingularVector q.1.1
        (torusShift (fun _ => 1) q.2.1) (torusShift (fun _ => 1) q.2.2) f) := by
    have hh := (hF.continuousAt (x := ((1,s₀),u₀))).tendsto.eventually hsep
    filter_upwards [hh] with q hq
    intro f hf
    have hfa := (hJ f).mp hf
    cases f with
    | inl b => exact hfa.1.elim
    | inr i => simpa only [torusShift_one_eq_angleTuple] using (hq i hfa.2).le
  have hdom := onsite_mem_inactiveDomain s₀ S
    hs₀ hS u₀ J hJ
  have hd : ∀ᶠ q : (ℝ × ℂ) × DoubleAngularVector N in 𝓝 ((1,s₀),u₀),
      q ∈ onsiteInactiveDomain J := (onsiteInactiveDomain_isOpen J).mem_nhds hdom
  obtain ⟨ρ,hρ,hball⟩ := Metric.eventually_nhds_iff.mp (hd.and he)
  exact ⟨e,δ,ρ,hδ,hρ,fun r s u h => hball h⟩

end
end IsingBulk.First
