import IsingBulk.First.ComplementInactiveNeighborhood
import IsingBulk.First.ComplementSimplex

/-! The selected source geometry produces a genuine fixed angular chart with
simultaneous inactive-factor regularity and active-factor separation. -/
namespace IsingBulk.First
noncomputable section
open Filter
open scoped Topology ContDiff

@[simp] theorem torusShift_one_eq_angleTuple {N : ℕ} (u : Fin N → ℝ) :
    torusShift (fun _ : Fin N => (1 : ℂ)) u = angleTuple 1 u := by
  funext i
  simp [torusShift, angleTuple, anglePoint_eq_angularCurve]

/-- Off the two selected bad configurations, one radius and one direction
work for the literal absolute-angle source factors on a fixed neighborhood.
Both the angular chart and direction are chosen before s or auxiliary values. -/
theorem selected_source_active_chart {p : ℕ} {a b : ℤ}
    (hp : p.Prime) (hp11 : 11 ≤ p)
    (ha : PrimeFamily.Admissible p a) (hb : PrimeFamily.Admissible p b)
    (s₀ : ℂ) (hs₀ : s₀ ≠ 0)
    (hS : sourceS s₀ = ((2*PrimeFamily.cosineAverage p a b : ℝ) : ℂ))
    (u₀ : DoubleAngularVector (2*p))
    (hgood : ¬ selectedBadConfiguration a b (angleTuple 1 u₀.1) (angleTuple 1 u₀.2))
    (J : Finset (SingularFactorIndex (2*p)))
    (hJ : ∀ f, f ∈ J ↔ singularFactorActive (angleTuple 1 u₀.1) (angleTuple 1 u₀.2)
      (2*PrimeFamily.cosineAverage p a b) f) :
    ∃ (e : DoubleAngularVector (2*p)) (δ ρ : ℝ), 0 < δ ∧ 0 < ρ ∧
      ∀ (r : ℝ) (s : ℂ) (u : DoubleAngularVector (2*p)),
      dist ((r,s),u) ((1,s₀),u₀) < ρ →
      ((r,s),u) ∈ sourceInactiveDomain J ∧
      ∀ f ∈ J, δ ≤ angularDot e (dampedSingularVector r
        (torusShift (fun _ => 1) u.1) (torusShift (fun _ => 1) u.2) f) := by
  have hx (i) : ‖angleTuple 1 u₀.1 i‖ = 1 := anglePoint_norm (by norm_num) _
  have hy (i) : ‖angleTuple 1 u₀.2 i‖ = 1 := anglePoint_norm (by norm_num) _
  obtain ⟨e,δ,hδ,hsep⟩ := selected_active_uniform_separator hp hp11 ha hb hx hy hgood
  let F : (ℝ × ℂ) × DoubleAngularVector (2*p) → ℝ × (Fin (2*p) → ℂ) × (Fin (2*p) → ℂ) :=
    fun q => (q.1.1,angleTuple 1 q.2.1,angleTuple 1 q.2.2)
  have hF : Continuous F := by
    exact continuous_fst.fst.prodMk
      (((angleTuple_continuous 1).comp continuous_snd.fst).prodMk
        ((angleTuple_continuous 1).comp continuous_snd.snd))
  have he : ∀ᶠ q : (ℝ × ℂ) × DoubleAngularVector (2*p) in 𝓝 ((1,s₀),u₀),
      ∀ f ∈ J, δ ≤ angularDot e (dampedSingularVector q.1.1
        (torusShift (fun _ => 1) q.2.1) (torusShift (fun _ => 1) q.2.2) f) := by
    have hh := (hF.continuousAt (x := ((1,s₀),u₀))).tendsto.eventually hsep
    filter_upwards [hh] with q hq
    intro f hf
    simpa only [torusShift_one_eq_angleTuple] using (hq f ((hJ f).mp hf)).le
  have hdom := selected_source_mem_inactiveDomain s₀ (2*PrimeFamily.cosineAverage p a b)
    hs₀ hS u₀ J hJ
  have hd : ∀ᶠ q : (ℝ × ℂ) × DoubleAngularVector (2*p) in 𝓝 ((1,s₀),u₀),
      q ∈ sourceInactiveDomain J := (sourceInactiveDomain_isOpen J).mem_nhds hdom
  obtain ⟨ρ,hρ,hball⟩ := Metric.eventually_nhds_iff.mp (hd.and he)
  exact ⟨e,δ,ρ,hδ,hρ,fun r s u h => hball h⟩

end
end IsingBulk.First
