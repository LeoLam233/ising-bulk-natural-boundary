import IsingBulk.AnisoF002.C03.NegativeDensityFactors

/-!
# Analytic full density through every collision divisor

The complete finite products are composed with the actual constrained
moving pole.  Analyticity uses the explicit filled factors, with no
division by a Vandermonde and no omitted coincident angles.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open IsingBulk.AnisoF002.Isotropic Set Filter
open scoped Topology BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem filledNegativeNumerator_analyticAt_comp {n : ℕ} {b : ℂ → ℂ}
    {g : ℂ × ℂ → ℂ} {d : ℂ} {T : E → ℂ} {v : E → Fin n → ℂ} {x : E}
    (hT : AnalyticAt ℂ T x) (hb : AnalyticAt ℂ b (T x))
    (hv : ∀ i, AnalyticAt ℂ (fun y => v y i) x)
    (hg : ∀ i, AnalyticAt ℂ g (T x, d + v x i))
    (hbody : ∀ i, Complex.sinh (g (T x, d + v x i)) ≠ 0)
    (hpair : ∀ ij ∈ indexPairs n,
      Complex.sinh ((g (T x, d + v x ij.1) + g (T x, d + v x ij.2)) / 2) ≠ 0) :
    AnalyticAt ℂ (fun y => filledNegativeNumerator n b g d (T y) (v y)) x := by
  have hγ (i : Fin n) : AnalyticAt ℂ (fun y => g (T y, d + v y i)) x :=
    (hg i).comp_of_eq (hT.prod (analyticAt_const.add (hv i))) rfl
  have hone : AnalyticAt ℂ (fun y => ∏ i, 1 / Complex.sinh (g (T y, d + v y i))) x := by
    apply Finset.analyticAt_fun_prod
    intro i _
    exact analyticAt_const.div (Complex.analyticAt_sinh.comp (hγ i)) (hbody i)
  have hpairs : AnalyticAt ℂ (fun y => ∏ ij ∈ indexPairs n,
      (complexSinc ((v y ij.1 - v y ij.2) / 2) /
        (2 * Complex.sinh ((g (T y, d + v y ij.1) + g (T y, d + v y ij.2)) / 2))) ^ 2) x := by
    apply Finset.analyticAt_fun_prod
    intro ij hij
    have hs := (complexSinc_analyticAt _).comp
      (((hv ij.1).sub (hv ij.2)).div_const (c := 2))
    have hd := (analyticAt_const (v := (2 : ℂ))).mul (Complex.analyticAt_sinh.comp
      (((hγ ij.1).add (hγ ij.2)).div_const (c := 2)))
    exact (hs.div hd (mul_ne_zero (by norm_num) (hpair ij hij))).pow 2
  exact (((hb.comp hT).pow (n ^ 2)).div_const.mul hone).mul hpairs

theorem completeNegativeNumerator_analyticAt_parameter {n : ℕ} {b : ℂ → ℂ}
    {g : ℂ × ℂ → ℂ} {d t : ℂ} {v : Fin n → ℂ}
    (hb : AnalyticAt ℂ b t) (hg : ∀ i, AnalyticAt ℂ g (t, d + v i))
    (hbody : ∀ i, Complex.sinh (g (t, d + v i)) ≠ 0)
    (hpair : ∀ ij ∈ indexPairs n,
      Complex.sinh ((g (t, d + v ij.1) + g (t, d + v ij.2)) / 2) ≠ 0) :
    AnalyticAt ℂ (fun s => completeNegativeNumerator n b g d s v) t := by
  have hfill : AnalyticAt ℂ (fun s => filledNegativeNumerator n b g d s v) t :=
    filledNegativeNumerator_analyticAt_comp analyticAt_id hb
      (fun _ => analyticAt_const) hg hbody hpair
  have hh : AnalyticAt ℂ (fun s => complexVandermondeSquared n v *
      filledNegativeNumerator n b g d s v) t := analyticAt_const.mul hfill
  simpa only [← completeNegativeNumerator_factorization] using hh

theorem phaseTemperatureSum_analyticAt_comp {n : ℕ} {g : ℂ × ℂ → ℂ} {d : ℂ}
    {T : E → ℂ} {v : E → Fin n → ℂ} {x : E}
    (hT : AnalyticAt ℂ T x) (hv : ∀ i, AnalyticAt ℂ (fun y => v y i) x)
    (hg : ∀ i, AnalyticAt ℂ g (T x, d + v x i)) :
    AnalyticAt ℂ (fun y => phaseTemperatureSum n g d (T y) (v y)) x := by
  apply Finset.analyticAt_fun_sum
  intro i _
  exact ((ContinuousLinearMap.apply ℂ ℂ ((1, 0) : ℂ × ℂ)).analyticAt _).comp
    ((hg i).fderiv.comp_of_eq (hT.prod (analyticAt_const.add (hv i))) rfl)

def filledNegativeDensityAt (n : ℕ) (b : ℂ → ℂ) (g : ℂ × ℂ → ℂ)
    (d t : ℂ) (v : Fin n → ℂ) : ℂ :=
  -(2 * filledNegativeNumerator n b g d t v) / phaseTemperatureSum n g d t v

theorem filledNegativeDensityAt_analyticAt_comp {n : ℕ} {b : ℂ → ℂ}
    {g : ℂ × ℂ → ℂ} {d : ℂ} {T : E → ℂ} {v : E → Fin n → ℂ} {x : E}
    (hT : AnalyticAt ℂ T x) (hb : AnalyticAt ℂ b (T x))
    (hv : ∀ i, AnalyticAt ℂ (fun y => v y i) x)
    (hg : ∀ i, AnalyticAt ℂ g (T x, d + v x i))
    (hbody : ∀ i, Complex.sinh (g (T x, d + v x i)) ≠ 0)
    (hpair : ∀ ij ∈ indexPairs n,
      Complex.sinh ((g (T x, d + v x ij.1) + g (T x, d + v x ij.2)) / 2) ≠ 0)
    (hD : phaseTemperatureSum n g d (T x) (v x) ≠ 0) :
    AnalyticAt ℂ (fun y => filledNegativeDensityAt n b g d (T y) (v y)) x := by
  exact (analyticAt_const.mul
    (filledNegativeNumerator_analyticAt_comp hT hb hv hg hbody hpair)).neg.div
      (phaseTemperatureSum_analyticAt_comp hT hv hg) hD

theorem completeNegativeNumerator_kernel_residue {n : ℕ} {b : ℂ → ℂ}
    {g : ℂ × ℂ → ℂ} {γ d t : ℂ} {v : Fin n → ℂ}
    (hb : AnalyticAt ℂ b t) (hg : ∀ i, AnalyticAt ℂ g (t, d + v i))
    (hbody : ∀ i, Complex.sinh (g (t, d + v i)) ≠ 0)
    (hpair : ∀ ij ∈ indexPairs n,
      Complex.sinh ((g (t, d + v ij.1) + g (t, d + v ij.2)) / 2) ≠ 0)
    (hlevel : (∑ i, g (t, d + v i)) = (n : ℂ) * γ)
    (hres : Complex.exp ((n : ℂ) * γ) = 1)
    (hD : deriv (centeredPhaseAverage n g γ d v) t ≠ 0) :
    Tendsto (fun s : ℂ => (s - t) *
      (completeNegativeNumerator n b g d s v *
        phasePoleKernel (fun u => ∑ i, g (u, d + v i)) s))
      (𝓝[≠] t) (𝓝 (-(complexVandermondeSquared n v * filledNegativeDensityAt n b g d t v))) := by
  have hd := phaseTemperatureSum_hasDerivAt n g d t v (fun i => (hg i).differentiableAt)
  have hd0 := phaseTemperatureSum_ne_zero_of_average (fun i => (hg i).differentiableAt) hD
  have hf := completeNegativeNumerator_analyticAt_parameter hb hg hbody hpair
  have hh := weighted_phasePoleKernel_residue hd (by simpa only [hlevel] using hres) hd0 hf.continuousAt
  convert hh using 1
  congr 1
  unfold filledNegativeDensityAt
  rw [completeNegativeNumerator_factorization]
  ring

end
end IsingBulk.AnisoF002.NegativeHT
