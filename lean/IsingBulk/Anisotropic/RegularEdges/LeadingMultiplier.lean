import IsingBulk.Anisotropic.RegularEdges.LeadingCoefficient
import IsingBulk.First.DominatedAnalyticIntegral
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

namespace IsingBulk.Anisotropic.RegularEdges
noncomputable section
open IsingBulk.First Set Filter
open scoped Topology BigOperators

/-- A genuine analytic prefactor multiplies the first singular coefficient by its value.
Every lower Leibniz term is proved to vanish using the already established lower-jet limits. -/
theorem analytic_multiplier_scaled_jet_limit {ι : Type*} {l : Filter ι}
    {w : ι→ℂ} {r : ι→ℝ} {f g : ℂ→ℂ} {k : ℕ} {C : ℂ}
    (hw : Tendsto w l (𝓝 0)) (hg : AnalyticAt ℂ g 0)
    (hf : ∀ᶠ x in l,AnalyticAt ℂ f (w x))
    (htop : Tendsto (fun x => r x • iteratedDeriv k f (w x)) l (𝓝 C))
    (hlower : ∀j<k,Tendsto (fun x => r x • iteratedDeriv j f (w x)) l (𝓝 0)) :
    Tendsto (fun x => r x • iteratedDeriv k (fun u => g u*f u) (w x)) l (𝓝 (g 0*C)) := by
  let T (i : ℕ) (x : ι) : ℂ := (k.choose i:ℂ)*iteratedDeriv i g (w x)*
    (r x • iteratedDeriv (k-i) f (w x))
  have hlim (i : ℕ) (hi : i∈Finset.range (k+1)) :
      Tendsto (T i) l (𝓝 (if i=0 then g 0*C else 0)) := by
    have hgi := (analyticAt_iteratedDeriv hg i).continuousAt.tendsto.comp hw
    by_cases hiz : i=0
    · subst i
      simpa [T] using hgi.mul htop
    · have hlt : k-i<k := by have := Finset.mem_range.mp hi; omega
      simpa [T,hiz] using (hgi.const_mul (k.choose i:ℂ)).mul (hlower (k-i) hlt)
  have hs := tendsto_finsetSum (Finset.range (k+1)) hlim
  simp only [Finset.sum_ite_eq',Finset.mem_range,Nat.zero_lt_succ,ite_true] at hs
  apply hs.congr'
  filter_upwards [hw.eventually hg.eventually_analyticAt,hf] with x hx hf'
  rw [iteratedDeriv_fun_mul hx.contDiffAt hf'.contDiffAt,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  dsimp [T]
  ring

theorem analytic_multiplier_scaled_lower_limit {ι : Type*} {l : Filter ι}
    {w : ι→ℂ} {r : ι→ℝ} {f g : ℂ→ℂ} {k j : ℕ}
    (hw : Tendsto w l (𝓝 0)) (hg : AnalyticAt ℂ g 0)
    (hf : ∀ᶠ x in l,AnalyticAt ℂ f (w x)) (hj : j<k)
    (hlower : ∀i<k,Tendsto (fun x => r x • iteratedDeriv i f (w x)) l (𝓝 0)) :
    Tendsto (fun x => r x • iteratedDeriv j (fun u => g u*f u) (w x)) l (𝓝 0) := by
  simpa only [mul_zero] using analytic_multiplier_scaled_jet_limit hw hg hf (hlower j hj)
    (fun i hi => hlower i (hi.trans hj))

/-- A bounded jet cannot contribute to a positively scaled first singular coefficient. -/
theorem bounded_jet_scaled_zero {a : ℕ} (ha : 0<a) {f : ℝ→ℂ}
    (hf : ∃ C : ℝ,∀ᶠ t : ℝ in 𝓝[>] 0,‖f t‖≤C) :
    Tendsto (fun t : ℝ => (t^a) • f t) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨C,hC⟩ := hf
  apply squeeze_zero_norm' (a := fun t : ℝ => ‖t^a‖*C)
  · filter_upwards [hC] with t ht
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left ht (norm_nonneg _)
  · have hh := ((tendsto_id : Tendsto (fun t : ℝ => t) (𝓝 0) (𝓝 0)).pow a).norm.mul_const C
    simpa [zero_pow (Nat.ne_of_gt ha)] using hh.mono_left nhdsWithin_le_nhds

end
end IsingBulk.Anisotropic.RegularEdges
