import IsingBulk.HT22.Geometry.FiniteEqualityCutoffs

namespace IsingBulk.HT22.Geometry
noncomputable section
open Set Filter Metric IsingBulk.First
open scoped Topology ContDiff

/-- Finite-center smooth cutoffs with an explicit uniform inner radius.
This generic construction is also valid when the relevant-center set is empty. -/
theorem exists_finite_center_cutoffs {ι E : Type*} [DecidableEq ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Finset ι) (center : ι → E) (R : ι → ℝ) (hR : ∀ i∈L,0<R i) :
    ∃ χ : ι → E → ℝ, ∃ r : ℝ,0<r ∧
      (∀ i∈L,ContDiff ℝ ∞ (χ i) ∧ HasCompactSupport (χ i) ∧
        (∀ x,0≤χ i x ∧ χ i x≤1) ∧ tsupport (χ i)⊆ball (center i) (R i)) ∧
      (∀ i∈L,∀ x,‖x-center i‖≤r → χ i x=1) := by
  classical
  have hex (i : {i : ι // i∈L}) : ∃ χ : E → ℝ,
      ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ (∀ x,0≤χ x ∧ χ x≤1) ∧
      χ =ᶠ[𝓝 (center i)] (fun _ => 1) ∧ tsupport χ ⊆ ball (center i) (R i) :=
    exists_fixed_smooth_cutoff (center i) (ball_mem_nhds _ (hR i i.2))
  choose χ hc hcomp hb hone hsupp using hex
  have hrad (i : {i : ι // i∈L}) : ∃ r : ℝ,0<r ∧ ∀ x∈ball (center i) r,χ i x=1 := by
    obtain ⟨r,hr,hb⟩ := Metric.mem_nhds_iff.mp (hone i)
    exact ⟨r,hr,hb⟩
  choose ρ hρ hρone using hrad
  let χ' : ι → E → ℝ := fun i => if hi : i∈L then χ ⟨i,hi⟩ else fun _ => 0
  let ρ' : ι → ℝ := fun i => if hi : i∈L then ρ ⟨i,hi⟩ else 1
  obtain ⟨r,hr,hsmall⟩ := finite_positive_radius L ρ' (fun i hi => by simpa only [ρ',dite_eq_left hi] using hρ ⟨i,hi⟩)
  refine ⟨χ',r,hr,?_,?_⟩
  · intro i hi
    simpa only [χ',dite_eq_left hi] using And.intro (hc ⟨i,hi⟩)
      (And.intro (hcomp ⟨i,hi⟩) (And.intro (hb ⟨i,hi⟩) (hsupp ⟨i,hi⟩)))
  · intro i hi x hx
    simp only [χ',dite_eq_left hi]
    apply hρone ⟨i,hi⟩
    rw [mem_ball,dist_eq_norm]
    exact hx.trans_lt (by simpa only [ρ',dite_eq_left hi] using hsmall i hi)

end
end IsingBulk.HT22.Geometry
