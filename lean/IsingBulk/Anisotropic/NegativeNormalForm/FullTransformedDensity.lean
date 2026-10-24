import IsingBulk.Anisotropic.NegativeNormalForm.CoincidenceFactors
import IsingBulk.Anisotropic.NegativeNormalForm.ConstrainedJacobian
import IsingBulk.Anisotropic.NegativeNormalForm.DensityAnalytic

/-! Full analytic pullback density: all original residue factors, the entire
Vandermonde multiplier, and the actual constrained Jacobian. Bounds here are
local analyticity statements, not dimension-uniform estimates. -/
noncomputable section
open Filter IsingBulk.First
open scoped Topology BigOperators
namespace IsingBulk.Anisotropic.NegativeNormalForm

def actualPairMultiplier {n : ℕ} (Phi : Config n → Config n) (v : Config n) : ℂ :=
  pairMultiplier (fun i j => coincidenceFactor Phi i j v)

 theorem actualPairMultiplier_analyticAt {n : ℕ} (Phi : Config n → Config n)
    (hPhi : AnalyticAt ℂ Phi 0) : AnalyticAt ℂ (actualPairMultiplier Phi) 0 := by
  apply Finset.analyticAt_fun_prod
  intro p _
  exact coincidenceFactor_analyticAt Phi hPhi p.1 p.2

@[simp] theorem actualPairMultiplier_zero {n : ℕ} (Phi : Config n → Config n)
    (hd : HasFDerivAt Phi (ContinuousLinearMap.id ℂ (Config n)) 0) :
    actualPairMultiplier Phi 0 = 1 := by
  apply Finset.prod_eq_one
  intro p hp
  exact coincidenceFactor_zero Phi hd p.1 p.2
    (ne_of_lt (mem_firstStrictPairs p |>.mp hp))

 theorem actual_vandermonde_pullback {n : ℕ} (Phi : Config n → Config n)
    (hPhi : AnalyticAt ℂ Phi 0)
    (heq : ∀ (e : Equiv.Perm (Fin n)) v, Phi (permute e v) = permute e (Phi v)) :
    ∀ᶠ v in 𝓝 (0 : Config n), vandermonde (Phi v)^2 =
      vandermonde v^2 * actualPairMultiplier Phi v^2 := by
  have he : ∀ᶠ v in 𝓝 (0 : Config n), ∀ i j, i < j →
      Phi v i - Phi v j = (v i-v j)*coincidenceFactor Phi i j v := by
    apply Filter.eventually_all.mpr
    intro i
    apply Filter.eventually_all.mpr
    intro j
    by_cases hij : i < j
    · exact (coincidenceFactor_identity Phi hPhi heq i j (ne_of_lt hij)).mono fun _ h _ => h
    · exact Filter.Eventually.of_forall fun _ h => (hij h).elim
  exact he.mono fun v hv => vandermonde_sq_dividedDifference v (Phi v) _ hv

 def fullTransformedDensity {m : ℕ} (B rootB : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi ≠ 0) (d : ℂ) (T : Config (m+1) → ℂ)
    (Phi : Config (m+1) → Config (m+1)) (u : Config m) : ℂ :=
  regularResidue B rootB phi hphi d T (Phi (freeChartCLM m u)) *
    actualPairMultiplier Phi (freeChartCLM m u)^2 * constrainedJacobian Phi u

 theorem fullTransformedDensity_analyticAt {m : ℕ} (B rootB : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi ≠ 0) (d : ℂ)
    (hB : AnalyticAt ℂ B (1-Complex.cos d)) (hBn : B (1-Complex.cos d) ≠ 0)
    (hr : AnalyticAt ℂ rootB (1-Complex.cos d))
    (T : Config (m+1) → ℂ) (hT : AnalyticAt ℂ T 0) (hT0 : T 0=1-Complex.cos d)
    (Phi : Config (m+1) → Config (m+1)) (hPhi : AnalyticAt ℂ Phi 0) (hPhi0 : Phi 0=0) :
    AnalyticAt ℂ (fullTransformedDensity B rootB phi hphi d T Phi) 0 := by
  have hR := regularResidue_analyticAt (Nat.succ_ne_zero m) B rootB phi hphi d hB hBn hr T hT hT0
  have hP := actualPairMultiplier_analyticAt Phi hPhi
  have hF := (freeChartCLM m).analyticAt 0
  exact (((hR.comp_of_eq hPhi hPhi0).comp_of_eq hF (map_zero _)).mul
    ((hP.comp_of_eq hF (map_zero _)).pow 2)).mul (constrainedJacobian_analyticAt Phi hPhi)

@[simp] theorem fullTransformedDensity_zero {m : ℕ} (B rootB : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi ≠ 0) (d : ℂ) (T : Config (m+1) → ℂ)
    (Phi : Config (m+1) → Config (m+1)) (hPhi0 : Phi 0=0)
    (hd : HasFDerivAt Phi (ContinuousLinearMap.id ℂ (Config (m+1))) 0) :
    fullTransformedDensity B rootB phi hphi d T Phi 0 = regularResidue B rootB phi hphi d T 0 := by
  simp [fullTransformedDensity,hPhi0,actualPairMultiplier_zero Phi hd,constrainedJacobian_zero Phi hd]

/-- Exact full-density pullback identity, including all collision divisors. -/
 theorem poleResidue_full_pullback {m : ℕ} (B rootB : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi ≠ 0) (d : ℂ) (T : Config (m+1) → ℂ)
    (Phi : Config (m+1) → Config (m+1)) (hPhi : AnalyticAt ℂ Phi 0)
    (heq : ∀ (e : Equiv.Perm (Fin (m+1))) v, Phi (permute e v)=permute e (Phi v)) :
    ∀ᶠ u in 𝓝 (0 : Config m),
      poleResidue B rootB phi hphi d T (Phi (freeChartCLM m u)) * constrainedJacobian Phi u =
        vandermonde (freeChartCLM m u)^2 * fullTransformedDensity B rootB phi hphi d T Phi u := by
  have ht : Tendsto (freeChartCLM m) (𝓝 0) (𝓝 0) := by
    simpa using ((freeChartCLM m).continuous.continuousAt (x := 0)).tendsto
  filter_upwards [ht.eventually (actual_vandermonde_pullback Phi hPhi heq)] with u hu
  rw [poleResidue_factor,hu]
  unfold fullTransformedDensity
  ring

 def normalizedFullDensity {m : ℕ} (B rootB : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi ≠ 0) (d : ℂ) (T : Config (m+1) → ℂ)
    (Phi : Config (m+1) → Config (m+1)) (u : Config m) : ℂ :=
  fullTransformedDensity B rootB phi hphi d T Phi u / regularResidue B rootB phi hphi d T 0

 theorem normalizedFullDensity_analyticAt {m : ℕ} (B rootB : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi ≠ 0) (d : ℂ)
    (hB : AnalyticAt ℂ B (1-Complex.cos d)) (hBn : B (1-Complex.cos d) ≠ 0)
    (hr : AnalyticAt ℂ rootB (1-Complex.cos d)) (hrn : rootB (1-Complex.cos d) ≠ 0)
    (T : Config (m+1) → ℂ) (hT : AnalyticAt ℂ T 0) (hT0 : T 0=1-Complex.cos d)
    (Phi : Config (m+1) → Config (m+1)) (hPhi : AnalyticAt ℂ Phi 0) (hPhi0 : Phi 0=0) :
    AnalyticAt ℂ (normalizedFullDensity B rootB phi hphi d T Phi) 0 := by
  exact (fullTransformedDensity_analyticAt B rootB phi hphi d hB hBn hr T hT hT0 Phi hPhi hPhi0).div
    analyticAt_const ((regularResidue_eventually_ne_zero (Nat.succ_ne_zero m) B rootB phi hphi d
      hB hBn hr hrn T hT hT0).self_of_nhds)

 theorem normalizedFullDensity_zero {m : ℕ} (B rootB : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi ≠ 0) (d : ℂ)
    (hB : AnalyticAt ℂ B (1-Complex.cos d)) (hBn : B (1-Complex.cos d) ≠ 0)
    (hr : AnalyticAt ℂ rootB (1-Complex.cos d)) (hrn : rootB (1-Complex.cos d) ≠ 0)
    (T : Config (m+1) → ℂ) (hT : AnalyticAt ℂ T 0) (hT0 : T 0=1-Complex.cos d)
    (Phi : Config (m+1) → Config (m+1)) (hPhi0 : Phi 0=0)
    (hd : HasFDerivAt Phi (ContinuousLinearMap.id ℂ (Config (m+1))) 0) :
    normalizedFullDensity B rootB phi hphi d T Phi 0 = 1 := by
  unfold normalizedFullDensity
  rw [fullTransformedDensity_zero B rootB phi hphi d T Phi hPhi0 hd]
  exact div_self ((regularResidue_eventually_ne_zero (Nat.succ_ne_zero m) B rootB phi hphi d
      hB hBn hr hrn T hT hT0).self_of_nhds)

end IsingBulk.Anisotropic.NegativeNormalForm
