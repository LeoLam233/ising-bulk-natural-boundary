import IsingBulk.Preferred22.ShellObligations
import IsingBulk.Preferred22.CoordinateDiameter

/-! A genuine smooth full-equality puncture, its exact real derivatives,
and the support and gradient bounds needed for transport flux. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set Filter Metric
open scoped BigOperators Topology ContDiff
set_option backward.isDefEq.respectTransparency false

/-- Squared Euclidean distance to the full-equality locus, up to the exact
factor 2N. Pair collisions alone are not removed. -/
def preferredEqualitySize {N : ℕ} (θ : Fin N → ℝ) : ℝ := ∑ a,∑ b,(θ a-θ b)^2

def preferredEqualityGradient {N : ℕ} (θ : Fin N → ℝ) (i : Fin N) : ℝ :=
  ∑ a,∑ b,2*(θ a-θ b)*((if a=i then 1 else 0)-(if b=i then 1 else 0))

/-- The cutoff equals zero on the small equality tube and one off it. -/
def preferredEqualityCutoff {N : ℕ} (R : ℝ) (θ : Fin N → ℝ) : ℝ :=
  preferredPopulationCutoff (preferredEqualitySize θ/R^2)

def preferredEqualityCutoffPartial {N : ℕ} (R : ℝ) (θ : Fin N → ℝ) (i : Fin N) : ℝ :=
  deriv (fun t : ℝ => preferredEqualityCutoff R (Function.update θ i t)) (θ i)

theorem preferredEqualitySize_nonneg {N : ℕ} (θ : Fin N → ℝ) : 0≤preferredEqualitySize θ :=
  Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))

theorem preferredEqualitySize_smooth {N : ℕ} : ContDiff ℝ ∞ (@preferredEqualitySize N) := by
  unfold preferredEqualitySize
  fun_prop

theorem preferredEqualityCutoff_smooth {N : ℕ} (R : ℝ) : ContDiff ℝ ∞ (@preferredEqualityCutoff N R) :=
  preferredPopulationCutoff_smooth.comp (preferredEqualitySize_smooth.div_const _)

/-- Exact partial derivative of the full pair-square puncture size. -/
theorem preferredEqualitySize_update_hasDerivAt {N : ℕ} (θ : Fin N → ℝ) (i : Fin N) :
    HasDerivAt (fun t : ℝ => preferredEqualitySize (Function.update θ i t))
      (preferredEqualityGradient θ i) (θ i) := by
  classical
  have hc (a : Fin N) : HasDerivAt (fun t : ℝ => Function.update θ i t a)
      (if a=i then 1 else 0) (θ i) := by
    by_cases ha : a=i
    · subst a
      convert hasDerivAt_id' (θ i) using 1 <;> simp
    · simpa [ha] using hasDerivAt_const (θ i) (θ a)
  unfold preferredEqualitySize preferredEqualityGradient
  apply HasDerivAt.fun_sum
  intro a _
  apply HasDerivAt.fun_sum
  intro b _
  convert ((hc a).sub (hc b)).pow 2 using 1
  ·
    simp only [Pi.sub_apply,Function.update_eq_self,Nat.cast_ofNat,Nat.add_one_sub_one,pow_one]

/-- The actual polynomial gradient costs at most four N squared times the
configuration diameter. No derivative of a maximum is taken. -/
theorem preferredEqualityGradient_norm {N : ℕ} (θ : Fin N → ℝ) (i : Fin N) :
    ‖preferredEqualityGradient θ i‖≤4*(N:ℝ)^2*preferredAngularDiameter θ := by
  classical
  have hdiam : 0≤preferredAngularDiameter θ := Metric.diam_nonneg
  have hb (a b : Fin N) :
      ‖2*(θ a-θ b)*((if a=i then 1 else 0)-(if b=i then 1 else 0))‖≤4*preferredAngularDiameter θ := by
    have hc : ‖((if a=i then (1:ℝ) else 0)-(if b=i then 1 else 0))‖≤2 := by
      split_ifs <;> norm_num
    calc
      _ = 2 * |θ a-θ b| * ‖((if a=i then (1:ℝ) else 0)-(if b=i then 1 else 0))‖ := by
        rw [norm_mul,norm_mul,Real.norm_eq_abs,Real.norm_eq_abs]
        norm_num
      _ ≤ (2*preferredAngularDiameter θ)*2 :=
        mul_le_mul (mul_le_mul_of_nonneg_left (preferredAngularDiameter_pair_le θ a b) (by norm_num))
          hc (norm_nonneg _) (by positivity)
      _ = _ := by ring
  unfold preferredEqualityGradient
  calc
    _ ≤ ∑ a : Fin N,∑ b : Fin N,‖2*(θ a-θ b)*((if a=i then 1 else 0)-(if b=i then 1 else 0))‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun a _ => norm_sum_le _ _))
    _ ≤ ∑ _a : Fin N,∑ _b : Fin N,4*preferredAngularDiameter θ :=
      Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun b _ => hb a b))
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]; ring

/-- The puncture size controls the entire diameter. -/
theorem preferredEqualitySize_diameter_sq {N : ℕ} (θ : Fin N → ℝ) :
    (preferredAngularDiameter θ)^2≤preferredEqualitySize θ := by
  have hpair (a b : Fin N) : (θ a-θ b)^2≤preferredEqualitySize θ := by
    exact (Finset.single_le_sum (fun c (_ : c∈Finset.univ) => sq_nonneg (θ a-θ c))
      (Finset.mem_univ b)).trans (Finset.single_le_sum
        (fun c (_ : c∈Finset.univ) => Finset.sum_nonneg (fun k _ => sq_nonneg (θ c-θ k)))
        (Finset.mem_univ a))
  have hd : preferredAngularDiameter θ≤Real.sqrt (preferredEqualitySize θ) := by
    apply Metric.diam_le_of_forall_dist_le (Real.sqrt_nonneg _)
    rintro _ ⟨a,rfl⟩ _ ⟨b,rfl⟩
    rw [Real.dist_eq]
    have hp := hpair a b
    nlinarith [Real.sq_sqrt (preferredEqualitySize_nonneg θ),sq_abs (θ a-θ b),
      abs_nonneg (θ a-θ b),Real.sqrt_nonneg (preferredEqualitySize θ)]
  exact (pow_le_pow_left₀ Metric.diam_nonneg hd 2).trans_eq (Real.sq_sqrt (preferredEqualitySize_nonneg θ))

/-- The actual population cutoff has a bounded derivative and exactly
constant outer tails. -/
theorem preferredPopulationCutoff_deriv_zero_upper {x : ℝ} (hx : 1/2<x) :
    deriv preferredPopulationCutoff x=0 := by
  have he : preferredPopulationCutoff =ᶠ[𝓝 x] (fun _ : ℝ => (1:ℝ)) := by
    filter_upwards [(Ioi_mem_nhds hx : Ioi (1/2:ℝ)∈𝓝 x)] with y hy
    exact preferredPopulationCutoff_one hy.le
  simpa only [deriv_const] using he.deriv_eq

theorem preferredPopulationCutoff_deriv_zero_lower {x : ℝ} (hx : x<1/4) :
    deriv preferredPopulationCutoff x=0 := by
  have he : preferredPopulationCutoff =ᶠ[𝓝 x] (fun _ : ℝ => (0:ℝ)) := by
    filter_upwards [(Iio_mem_nhds hx : Iio (1/4:ℝ)∈𝓝 x)] with y hy
    exact preferredPopulationCutoff_zero hy.le
  simpa only [deriv_const] using he.deriv_eq

theorem preferredPopulationCutoff_deriv_bounded :
    ∃ C : ℝ,0<C ∧ ∀ x : ℝ,‖deriv preferredPopulationCutoff x‖≤C := by
  obtain ⟨A,hA⟩ := (isCompact_Icc : IsCompact (Icc (0:ℝ) 1)).exists_bound_of_continuousOn
    (preferredPopulationCutoff_smooth.continuous_deriv (by simp)).continuousOn
  refine ⟨max A 1,zero_lt_one.trans_le (le_max_right _ _),?_⟩
  intro x
  by_cases hx0 : 0≤x
  · by_cases hx1 : x≤1
    · exact (hA x ⟨hx0,hx1⟩).trans (le_max_left _ _)
    · rw [preferredPopulationCutoff_deriv_zero_upper (by linarith),norm_zero]
      exact zero_le_one.trans (le_max_right _ _)
  · rw [preferredPopulationCutoff_deriv_zero_lower (by linarith),norm_zero]
    exact zero_le_one.trans (le_max_right _ _)

/-- Exact derivative of the smooth puncture, before estimating its flux. -/
theorem preferredEqualityCutoffPartial_formula {N : ℕ} (R : ℝ) (θ : Fin N → ℝ) (i : Fin N) :
    preferredEqualityCutoffPartial R θ i=
      deriv preferredPopulationCutoff (preferredEqualitySize θ/R^2)*preferredEqualityGradient θ i/R^2 := by
  have hh := (preferredPopulationCutoff_smooth.differentiable (by simp)
    (preferredEqualitySize (Function.update θ i (θ i))/R^2)).hasDerivAt.comp (θ i)
    ((preferredEqualitySize_update_hasDerivAt θ i).div_const (R^2))
  simpa only [preferredEqualityCutoffPartial,preferredEqualityCutoff,Function.update_eq_self,
    Function.comp_def,mul_div_assoc] using hh.deriv

/-- Outside the actual equality tube every puncture partial vanishes. -/
theorem preferredEqualityCutoffPartial_zero_of_diameter_lt {N : ℕ} {R : ℝ} (hR : 0<R)
    (θ : Fin N → ℝ) (i : Fin N) (hd : R<preferredAngularDiameter θ) :
    preferredEqualityCutoffPartial R θ i=0 := by
  have hs := preferredEqualitySize_diameter_sq θ
  have hx : (1/2:ℝ)<preferredEqualitySize θ/R^2 := by
    apply (lt_div_iff₀ (sq_pos_of_pos hR)).mpr
    nlinarith [sq_nonneg (preferredAngularDiameter θ-R)]
  rw [preferredEqualityCutoffPartial_formula,preferredPopulationCutoff_deriv_zero_upper hx,zero_mul,zero_div]

/-- Uniform first derivatives of the actual smooth puncture; the factor of
diameter cancels the actual V singularity in the boundary current. -/
theorem preferredEqualityCutoffPartial_bound :
    ∃ C : ℝ,0<C ∧ ∀ N : ℕ,∀ R : ℝ,0<R → ∀ θ : Fin N → ℝ,∀ i : Fin N,
      ‖preferredEqualityCutoffPartial R θ i‖≤C*(N:ℝ)^2*preferredAngularDiameter θ/R^2 := by
  obtain ⟨C,hC,hη⟩ := preferredPopulationCutoff_deriv_bounded
  refine ⟨4*C,by positivity,?_⟩
  intro N R hR θ i
  rw [preferredEqualityCutoffPartial_formula,norm_div,norm_mul,Real.norm_of_nonneg (sq_nonneg R)]
  calc
    _ ≤ (C*(4*(N:ℝ)^2*preferredAngularDiameter θ))/R^2 := div_le_div_of_nonneg_right
      (mul_le_mul (hη _) (preferredEqualityGradient_norm θ i) (norm_nonneg _) hC.le) (sq_nonneg R)
    _ = _ := by ring

end
end IsingBulk.Preferred22
