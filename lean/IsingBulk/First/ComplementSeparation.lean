import IsingBulk.First.ComplementVectors

/-! Uniform persistence of the actual active-vector separator under contour damping. -/
namespace IsingBulk.First
noncomputable section
open scoped BigOperators Topology
open Filter Set

/-- Ordinary real directional pairing on the two angular coordinate blocks. -/
def angularDot {N : ℕ} (e v : DoubleAngularVector N) : ℝ :=
  (∑ i, e.1 i * v.1 i) + ∑ i, e.2 i * v.2 i

/-- Coordinates of a real functional as a genuine angular direction. -/
def separatingDirection {N : ℕ} (f : StrongDual ℝ (DoubleAngularVector N)) :
    DoubleAngularVector N :=
  (fun i => f (Pi.single i 1, 0), fun i => f (0, Pi.single i 1))

theorem angularDot_separatingDirection {N : ℕ}
    (f : StrongDual ℝ (DoubleAngularVector N)) (v : DoubleAngularVector N) :
    angularDot (separatingDirection f) v = f v := by
  classical
  have hv : v = (∑ i, v.1 i • (Pi.single i 1, (0 : Fin N → ℝ))) +
      ∑ i, v.2 i • ((0 : Fin N → ℝ), Pi.single i 1) := by
    ext i <;> simp [Prod.fst_sum, Prod.snd_sum, Finset.sum_apply, Pi.single_apply]
  conv_rhs => rw [hv]
  simp only [map_add, map_sum, map_smul, smul_eq_mul]
  simp [angularDot, separatingDirection, mul_comm]

/-- Imaginary gradient of each source exponential on a common radius r.
The torus coordinates x,y are angular positions before multiplying by r. -/
def dampedSingularVector {N : ℕ} (r : ℝ) (x y : Fin N → ℂ) :
    SingularFactorIndex N → DoubleAngularVector N
  | .inl false => (fun _ => r ^ N * (∏ i, x i).re, 0)
  | .inl true => (0, fun _ => r ^ N * (∏ i, y i).re)
  | .inr (.inl (false, i, j)) =>
      ((r ^ 2 * (x i * x j).re) • (Pi.single i (1 : ℝ) + Pi.single j 1), 0)
  | .inr (.inl (true, i, j)) =>
      (0, (r ^ 2 * (y i * y j).re) • (Pi.single i (1 : ℝ) + Pi.single j 1))
  | .inr (.inr i) =>
      (Pi.single i ((r + r⁻¹) / 2 * (x i).im),
       Pi.single i ((r + r⁻¹) / 2 * (y i).im))

/-- At unit radius every active damped vector is exactly the source vector. -/
theorem dampedSingularVector_one {N : ℕ} {x y : Fin N → ℂ} {S : ℝ}
    {i : SingularFactorIndex N} (hi : singularFactorActive x y S i) :
    dampedSingularVector 1 x y i = singularFactorVector x y i := by
  rcases i with b | (⟨b, i, j⟩ | i)
  · cases b <;> simp_all [singularFactorActive, dampedSingularVector, singularFactorVector] <;> rfl
  · cases b <;> simp_all [singularFactorActive, dampedSingularVector, singularFactorVector]
  · simp [dampedSingularVector, singularFactorVector]

/-- Actual perturbed vectors are continuous at unit radius. -/
theorem dampedSingularVector_continuousAt {N : ℕ} (x y : Fin N → ℂ)
    (i : SingularFactorIndex N) :
    ContinuousAt (fun q : ℝ × (Fin N → ℂ) × (Fin N → ℂ) =>
      dampedSingularVector q.1 q.2.1 q.2.2 i) (1, x, y) := by
  rcases i with b | (⟨b, i, j⟩ | i)
  · cases b <;> unfold dampedSingularVector <;> fun_prop
  · cases b <;> unfold dampedSingularVector <;> fun_prop
  · change ContinuousAt (fun q : ℝ × (Fin N → ℂ) × (Fin N → ℂ) =>
      ((Pi.single i ((q.1 + q.1⁻¹) / 2 * (q.2.1 i).im),
       Pi.single i ((q.1 + q.1⁻¹) / 2 * (q.2.2 i).im)) : DoubleAngularVector N)) (1, x, y)
    apply ContinuousAt.prodMk
    all_goals
      apply continuousAt_pi.2
      intro j
      simp only [Pi.single_apply]
      split_ifs <;> fun_prop (disch := norm_num)

/-- The fixed separator survives on one common neighborhood of the base torus
point and unit radius. All active factors share the same positive margin. -/
theorem selected_active_uniform_separator {p : ℕ} {a b : ℤ}
    {x y : Fin (2*p) → ℂ} (hp : p.Prime) (hp11 : 11 ≤ p)
    (ha : PrimeFamily.Admissible p a) (hb : PrimeFamily.Admissible p b)
    (hx : ∀ i, ‖x i‖ = 1) (hy : ∀ i, ‖y i‖ = 1)
    (hgood : ¬ selectedBadConfiguration a b x y) :
    ∃ (e : DoubleAngularVector (2*p)) (δ : ℝ), 0 < δ ∧
      ∀ᶠ q : ℝ × (Fin (2*p) → ℂ) × (Fin (2*p) → ℂ) in 𝓝 (1, x, y),
        ∀ i, singularFactorActive x y (2 * PrimeFamily.cosineAverage p a b) i →
          δ < angularDot e (dampedSingularVector q.1 q.2.1 q.2.2 i) := by
  obtain ⟨f, δ, hδ, hf⟩ := selected_active_separating_functional hp hp11 ha hb hx hy hgood
  refine ⟨separatingDirection f, δ / 2, by linarith, ?_⟩
  rw [Filter.eventually_all]
  intro i
  by_cases hi : singularFactorActive x y (2 * PrimeFamily.cosineAverage p a b) i
  · have hc := f.continuous.continuousAt.comp (dampedSingularVector_continuousAt x y i)
    have hbase : δ / 2 < f (dampedSingularVector 1 x y i) := by
      rw [dampedSingularVector_one hi]
      linarith [hf i hi]
    have he := hc.preimage_mem_nhds (Ioi_mem_nhds hbase)
    filter_upwards [he] with q hq
    intro _
    rw [angularDot_separatingDirection]
    exact hq
  · exact Filter.Eventually.of_forall (fun _ hi' => False.elim (hi hi'))

end
end IsingBulk.First
