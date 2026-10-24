import IsingBulk.Anisotropic.NegativeNormalForm.ImplicitPole

/-! A genuinely permutation-invariant analytic pole, selected by finite
symmetrization of the actual unique implicit solution. -/
namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open scoped Topology BigOperators

def permuteCLM {n : ℕ} (e : Equiv.Perm (Fin n)) : Config n →L[ℂ] Config n :=
  ContinuousLinearMap.pi (fun i => ContinuousLinearMap.proj (e i))

@[simp] theorem permuteCLM_apply {n : ℕ} (e : Equiv.Perm (Fin n)) (v : Config n) :
    permuteCLM e v = permute e v := rfl

def permutationAverage {n : ℕ} (T : Config n → ℂ) (v : Config n) : ℂ :=
  (∑ e : Equiv.Perm (Fin n), T (permute e v)) / Fintype.card (Equiv.Perm (Fin n))

theorem permutationAverage_permute {n : ℕ} (T : Config n → ℂ)
    (v : Config n) (e : Equiv.Perm (Fin n)) :
    permutationAverage T (permute e v) = permutationAverage T v := by
  unfold permutationAverage
  congr 1
  simpa [permute, Function.comp_def] using
    Equiv.sum_comp (Equiv.mulLeft e) (fun f => T (permute f v))

@[simp] theorem permutationAverage_zero {n : ℕ} (T : Config n → ℂ) :
    permutationAverage T 0 = T 0 := by
  have hc : (Fintype.card (Equiv.Perm (Fin n)) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  simp [permutationAverage, permute, hc]

/-- The local uniqueness theorem forces permutation invariance of the germ. -/
theorem implicitPole_eventually_permute {n : ℕ} (B : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi ≠ 0) (d : ℂ) (T : Config n → ℂ)
    (hT : ContinuousAt T 0) (hT0 : T 0 = 1-Complex.cos d)
    (hsol : ∀ᶠ v in 𝓝 (0 : Config n), poleEquation B phi hphi d (T v) v = 0)
    (huniq : ∀ᶠ z : Config n × ℂ in 𝓝 (0, 1-Complex.cos d),
      poleEquation B phi hphi d z.2 z.1 = 0 ↔ T z.1 = z.2)
    (e : Equiv.Perm (Fin n)) :
    ∀ᶠ v in 𝓝 (0 : Config n), T (permute e v) = T v := by
  have hp : Filter.Tendsto (fun v : Config n => (permute e v, T v))
      (𝓝 0) (𝓝 (0, 1-Complex.cos d)) := by
    simpa only [map_zero, permuteCLM_apply, hT0] using
      ((permuteCLM e).continuous.tendsto (0 : Config n)).prodMk_nhds hT.tendsto
  filter_upwards [hsol, hp.eventually huniq] with v hv hu
  exact hu.mp (by simpa only [poleEquation_permute] using hv)

/-- No abstract equivariant normal form is assumed: the pole solves the actual
phase sum and is symmetrized only after proving equality of all permutation germs. -/
theorem exists_permutation_invariant_pole {n : ℕ} (hn : n ≠ 0)
    (B : ℂ → ℂ) (phi : ℝ) (hphi : Real.sin phi ≠ 0) (d : ℂ)
    (hB : AnalyticAt ℂ B (1-Complex.cos d)) (hBn : B (1-Complex.cos d) ≠ 0) :
    ∃ T : Config n → ℂ,
      AnalyticAt ℂ T 0 ∧ T 0 = 1-Complex.cos d ∧
      (∀ᶠ v in 𝓝 (0 : Config n), poleEquation B phi hphi d (T v) v = 0) ∧
      (∀ e : Equiv.Perm (Fin n), ∀ v, T (permute e v) = T v) := by
  obtain ⟨T, hT, hT0, hsol, huniq⟩ := exists_analytic_implicit_pole hn B phi hphi d hB hBn
  have hall : ∀ᶠ v in 𝓝 (0 : Config n), ∀ e : Equiv.Perm (Fin n), T (permute e v) = T v :=
    Filter.eventually_all.mpr (fun e => implicitPole_eventually_permute B phi hphi d T
      hT.continuousAt hT0 hsol huniq e)
  have heq : permutationAverage T =ᶠ[𝓝 (0 : Config n)] T := by
    filter_upwards [hall] with v hv
    have hc : (Fintype.card (Equiv.Perm (Fin n)) : ℂ) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    simp [permutationAverage, hv, hc]
  refine ⟨permutationAverage T, hT.congr heq.symm, by simpa using hT0, ?_, ?_⟩
  · filter_upwards [hsol, heq] with v hv he
    simpa only [he] using hv
  · exact fun e v => permutationAverage_permute T v e

end
end IsingBulk.Anisotropic.NegativeNormalForm
