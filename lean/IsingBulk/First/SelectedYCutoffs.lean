import IsingBulk.First.CompatibleYCutoffAtDelta

/-! The two-center cutoff construction instantiated from the immutable
prime-family angle data, with no informal distinct-center premise. -/
namespace IsingBulk.First
noncomputable section
open Complex Set Filter
open scoped Topology

theorem prime_angle_ne {p : ℕ} (hp : p.Prime) {a b : ℤ} (hab : a ≠ b) :
    IsingBulk.PrimeFamily.angle p a ≠ IsingBulk.PrimeFamily.angle p b := by
  intro he
  have hp0 : (p:ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hh := congrArg (fun x : ℝ => x*((p:ℝ)/(2*Real.pi))) he
  simp only [IsingBulk.PrimeFamily.angle] at hh
  field_simp [hp0,Real.pi_ne_zero] at hh
  exact hab (by exact_mod_cast hh)

theorem selected_y_centers_ne {p : ℕ} (hp : p.Prime) {a b : ℤ}
    (ha : IsingBulk.PrimeFamily.Admissible p a) (hb : IsingBulk.PrimeFamily.Admissible p b)
    (hab : a ≠ b) :
    exp (-(IsingBulk.PrimeFamily.angle p a:ℂ)*I) ≠
      exp (-(IsingBulk.PrimeFamily.angle p b:ℂ)*I) :=
  ordered_chart_centers_ne (selectedOrderedChart ha hb) (prime_angle_ne hp hab)

theorem selected_cutoff_delta_bound_pos {p : ℕ} (hp : p.Prime) {a b : ℤ}
    (ha : IsingBulk.PrimeFamily.Admissible p a) (hb : IsingBulk.PrimeFamily.Admissible p b)
    (hab : a ≠ b) :
    0 < compatibleCutoffDeltaBound (IsingBulk.PrimeFamily.angle p a) (IsingBulk.PrimeFamily.angle p b) :=
  compatibleCutoffDeltaBound_pos (selected_y_centers_ne hp ha hb hab)

/-- The cutoff threshold is fixed from source prime/angle data. Once the
common mean half-width is chosen below it, the exact same half-width is used
by both constructed periodic charts and their actual complement. -/
theorem selected_compatible_y_cutoffs {p : ℕ} (hp : p.Prime) {a b : ℤ}
    (ha : IsingBulk.PrimeFamily.Admissible p a) (hb : IsingBulk.PrimeFamily.Admissible p b)
    (hab : a ≠ b) :
    ∃ D : ℝ, 0 < D ∧ ∀ delta : ℝ, 0 < delta → delta ≤ D →
      ∀ U : Set (Fin (2*p-1) → ℝ), U ∈ 𝓝 0 → ∀ Hmax : ℝ, 0 < Hmax →
      ∃ c : CompatibleYCutoffData (2*p-1) (IsingBulk.PrimeFamily.angle p a)
        (IsingBulk.PrimeFamily.angle p b) U, c.delta=delta ∧ c.H ≤ Hmax := by
  refine ⟨_,selected_cutoff_delta_bound_pos hp ha hb hab,?_⟩
  intro delta hd hdD U hU Hmax hH
  exact exists_compatibleYCutoffData_at_delta (2*p-1) _ _ hU hH hd hdD

end
end IsingBulk.First
