import IsingBulk.First.ActualLowerDerivativeBound
import IsingBulk.First.ActualPostMeanInterchange

/-! Every derivative below the first singular order is uniformly bounded for
one common fixed shape cutoff. Actual outer parameter differentiation has
already been justified before the fixed-ball majorant is applied. -/
namespace IsingBulk.First
noncomputable section
open Complex MeasureTheory Set Filter Metric IsingBulk.Branch
open scoped Topology

private theorem lower_finite_positive_min {ι : Type*} (S : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ S, 0 < f i) : ∃ r : ℝ, 0 < r ∧ ∀ i ∈ S, r ≤ f i := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1,by norm_num,by simp⟩
  | @insert i S hi ih =>
    obtain ⟨r,hr,hb⟩ := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
    refine ⟨min (f i) r,lt_min (hf i (Finset.mem_insert_self _ _)) hr,?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (hb j hj)

theorem actual_postMean_lower_integral_bounds {n k : ℕ} (hn : 1 ≤ n)
    (hdegree : n-1+(n+1)*n = 2*k) (a : OrderedChartData)
    (ha : exp (-(n+1:ℂ)*(a.alpha:ℂ)*I)=1)
    (hb : exp (-(n+1:ℂ)*(a.beta:ℂ)*I)=1) :
    ∃ R : ℝ, 0 < R ∧ ∀ chi : ShapeSpace n → ℂ,
      Continuous chi → (∀ x, ‖chi x‖ ≤ 1) → (∀ x, chi x ≠ 0 → ‖x‖ < R) →
      ∀ j : ℕ, j < k → ∃ C : ℝ, 0 < C ∧ ∀ epsilon : ℝ,
        0 < epsilon → epsilon < R →
        ‖(deriv^[j] (localizedPostMeanIntegral a chi)) (radialParameter a.theta epsilon)‖ ≤ C := by
  classical
  have hFixed (i : Fin k) := actual_lower_postMean_shape_bound hn hdegree i.2 a hb
  choose radius bound hr hB hBound using hFixed
  obtain ⟨R₀,hR₀,hmin⟩ := lower_finite_positive_min Finset.univ radius (fun i _ => hr i)
  obtain ⟨Ri,hRi,hInt⟩ := intrinsic_postMean_integral_interchange (n := n) a ha hb
  let R := min R₀ Ri
  have hR : 0 < R := lt_min hR₀ hRi
  have hRI : R ≤ Ri := min_le_right _ _
  have hRj (i : Fin k) : R ≤ radius i := (min_le_left _ _).trans (hmin i (Finset.mem_univ i))
  refine ⟨R,hR,?_⟩
  intro chi hchi hchib hchis j hj
  let i : Fin k := ⟨j,hj⟩
  let c : ℂ := ((Real.sqrt (n+1))⁻¹:ℝ)
  have hf : localizedPostMeanIntegral a chi = fun s => c*intrinsicPostMeanIntegral a chi s := by
    funext s
    rw [localizedPostMeanIntegral_eq_intrinsic,Complex.real_smul]
  have hBi : 0 < bound i := hB i
  refine ⟨‖c‖*bound i+1,by positivity,?_⟩
  intro epsilon he heR
  rw [hf,iterate_deriv_const_mul]
  dsimp only
  rw [hInt epsilon he (heR.trans_le hRI) chi hchi (fun x hx => (hchis x hx).trans_le hRI) j,norm_mul]
  have hbnd := (hBound i chi hchi hchib (fun x hx => (hchis x hx).trans_le (hRj i))
    epsilon he (heR.trans_le (hRj i))).2
  exact (mul_le_mul_of_nonneg_left hbnd (norm_nonneg c)).trans (by linarith)

/-- The actual j<k clause uses one cutoff neighborhood for all lower orders,
where k=N²/2−1 is the manuscript's first singular derivative index. -/
theorem actual_first_postMean_lower_bounds {n : ℕ} (hn : 1 ≤ n) (a : OrderedChartData)
    (heven : Even (n+1))
    (ha : exp (-(n+1:ℂ)*(a.alpha:ℂ)*I)=1)
    (hb : exp (-(n+1:ℂ)*(a.beta:ℂ)*I)=1) :
    ∃ R : ℝ, 0 < R ∧ ∀ chi : ShapeSpace n → ℂ,
      Continuous chi → (∀ x, ‖chi x‖ ≤ 1) → (∀ x, chi x ≠ 0 → ‖x‖ < R) →
      ∀ j : ℕ, j < (n+1)^2/2-1 → ∃ C : ℝ, 0 < C ∧ ∀ epsilon : ℝ,
        0 < epsilon → epsilon < R →
        ‖(deriv^[j] (localizedPostMeanIntegral a chi)) (radialParameter a.theta epsilon)‖ ≤ C :=
  actual_postMean_lower_integral_bounds hn (source_shape_radial_exponent hn heven) a ha hb

end
end IsingBulk.First
