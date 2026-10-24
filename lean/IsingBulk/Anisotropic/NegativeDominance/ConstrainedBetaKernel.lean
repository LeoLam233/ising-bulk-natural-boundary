import IsingBulk.Anisotropic.NegativeNormalForm.ShapePeriodExact
import IsingBulk.First.ShapeSource
import IsingBulk.Anisotropic.NegativeDominance.SmallConstrainedBall

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open IsingBulk.First IsingBulk.Anisotropic.NegativeNormalForm MeasureTheory Set
open scoped BigOperators

def constrainedBetaKernel (n j : ℕ) (τ c : ℝ) (x : Fin n→ℝ) : ℝ :=
  firstVandermonde (shapeExtend x)^2/(τ+c*(∑i : Fin (n+1),(shapeExtend x i)^2))^(j+1)

def constrainedBetaValue (N j : ℕ) (τ c : ℝ) : ℝ :=
  ((N.factorial : ℝ)*Real.pi^((N-1)/2)*factorialProduct N/Real.sqrt N)*
    ((j-alpha N).factorial : ℝ)/(c^(alpha N)*τ^(j+1-alpha N)*j.factorial)

theorem sum_shapeExtend_sq {n : ℕ} (x : Fin n→ℝ) :
    (∑i : Fin (n+1),(shapeExtend x i)^2)=(∑i,(x i)^2)+(∑i,x i)^2 := by
  rw [Fin.sum_univ_castSucc]
  simp

theorem constrainedBetaKernel_period (n j : ℕ) (τ c : ℝ) :
    (((∫x : Fin n→ℝ,constrainedBetaKernel n j τ c x) : ℝ) : ℂ)=shapePeriod n j τ (c : ℂ) := by
  rw [shapePeriod_eq_sourceIntegral,←integral_complex_ofReal]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  simp only [constrainedBetaKernel,sum_shapeExtend_sq,Complex.ofReal_div,Complex.ofReal_pow,
    Complex.ofReal_add,Complex.ofReal_mul]

theorem constrainedBetaKernel_integral {n : ℕ} (ho : Odd (n+1)) (hn : 2≤n)
    (j : ℕ) (hj : alpha (n+1)≤j) (τ c : ℝ) (hτ : 0<τ) (hc : 0<c) :
    (∫x : Fin n→ℝ,constrainedBetaKernel n j τ c x)=constrainedBetaValue (n+1) j τ c := by
  apply Complex.ofReal_injective
  rw [constrainedBetaKernel_period]
  have he := shapePeriod_factorial ho (by omega) j hj τ c hτ hc
  simpa only [constrainedBetaValue,Nat.add_sub_cancel] using he

theorem constrainedBetaValue_pos {N : ℕ} (hN : 0<N) (j : ℕ) {τ c : ℝ}
    (hτ : 0<τ) (hc : 0<c) : 0<constrainedBetaValue N j τ c := by
  have hF := factorialProduct_pos N
  unfold constrainedBetaValue
  positivity

theorem constrainedBetaKernel_integrable {n : ℕ} (ho : Odd (n+1)) (hn : 2≤n)
    (j : ℕ) (hj : alpha (n+1)≤j) (τ c : ℝ) (hτ : 0<τ) (hc : 0<c) :
    Integrable (constrainedBetaKernel n j τ c) := by
  apply Integrable.of_integral_ne_zero
  rw [constrainedBetaKernel_integral ho hn j hj τ c hτ hc]
  exact (constrainedBetaValue_pos (by omega) j hτ hc).ne'

theorem constrainedBetaKernel_nonneg (n j : ℕ) {τ c : ℝ} (hτ : 0≤τ) (hc : 0≤c)
    (x : Fin n→ℝ) : 0≤constrainedBetaKernel n j τ c x := by
  unfold constrainedBetaKernel
  positivity

/-- Exact full-dimensional beta domination for actual residue integrals on
arbitrary measurable cutoff sectors. -/
theorem norm_integral_constrained_beta_bound {n : ℕ} (ho : Odd (n+1)) (hn : 2≤n)
    (j : ℕ) (hj : alpha (n+1)≤j) (τ c : ℝ) (hτ : 0<τ) (hc : 0<c)
    (S : Set (Fin n→ℝ)) (hS : MeasurableSet S) (f : (Fin n→ℝ)→ℂ)
    (K : ℝ) (hK : 0≤K) (hf : ∀x∈S,‖f x‖≤K*constrainedBetaKernel n j τ c x) :
    ‖∫x in S,f x‖≤K*constrainedBetaValue (n+1) j τ c := by
  have hi := (constrainedBetaKernel_integrable ho hn j hj τ c hτ hc).const_mul K
  calc
    _ ≤ ∫x in S,K*constrainedBetaKernel n j τ c x :=
      norm_integral_le_of_norm_le hi.integrableOn (ae_restrict_of_forall_mem hS hf)
    _ ≤ ∫x,K*constrainedBetaKernel n j τ c x :=
      setIntegral_le_integral hi (Filter.Eventually.of_forall (fun x =>
        mul_nonneg hK (constrainedBetaKernel_nonneg n j hτ.le hc.le x)))
    _ = _ := by rw [integral_const_mul,constrainedBetaKernel_integral ho hn j hj τ c hτ hc]

end
end IsingBulk.Anisotropic.NegativeDominance
