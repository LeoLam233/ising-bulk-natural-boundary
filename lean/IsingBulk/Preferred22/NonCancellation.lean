import IsingBulk.Preferred22.NormalConvergence
import IsingBulk.Preferred22.NaturalBoundary

/-! Exact noncancellation assembly for the actual complete particle series.
The first-coefficient limit, finite complement and boundary tail are explicit
remaining premises. This module does not assert that those premises are proved. -/
namespace IsingBulk.Preferred22
noncomputable section
open Complex Set Filter
open scoped BigOperators Topology

def PreferredFirstSingularityStatement (ζ : ℂ) (Nstar k : ℕ) : Prop :=
  ∃ Λ : ℂ, Λ ≠ 0 ∧ Tendsto (fun eps : ℝ => Real.sqrt eps •
    iteratedDeriv k (coefficient Nstar) ((1+(eps:ℂ))*ζ)) (𝓝[>] 0) (𝓝 Λ)

def PreferredFiniteComplementStatement (ζ : ℂ) (m k : ℕ) : Prop :=
  ∃ C eps0 : ℝ, 0 < C ∧ 0 < eps0 ∧ ∀ eps : ℝ, 0 < eps → eps < eps0 →
    (∑ n ∈ Finset.range m,
      ‖iteratedDeriv k (coefficient (2*(n+1))) ((1+(eps:ℂ))*ζ)‖) ≤ C

theorem even_coefficient_derivatives_absolutely_summable (j : ℕ) {s : ℂ}
    (hs : 1 < ‖s‖) :
    Summable (fun n : ℕ => ‖iteratedDeriv j (coefficient (2*(n+1))) s‖) := by
  obtain ⟨u,hu,hbound⟩ := compact_even_derivative_majorant (isCompact_singleton (x := s))
    (by intro t ht; simpa only [mem_singleton_iff.mp ht] using hs) j
  exact hu.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => hbound n s (mem_singleton s))

theorem evenSeries_derivative_split (j m : ℕ) {s : ℂ} (hs : 1 < ‖s‖) :
    iteratedDeriv j evenSeries s =
      (∑ n ∈ Finset.range m,iteratedDeriv j (coefficient (2*(n+1))) s) +
      iteratedDeriv j (coefficient (2*(m+1))) s +
      ∑' n : ℕ,iteratedDeriv j (coefficient (2*(n+m+2))) s := by
  rw [iteratedDeriv_evenSeries j hs]
  have h := (even_coefficient_derivatives_absolutely_summable j hs).of_norm.sum_add_tsum_nat_add (m+1)
  rw [Finset.sum_range_succ] at h
  convert h.symm using 1

theorem actualHigherTail_eq_shifted (ζ : ℂ) (m j : ℕ) (eps : ℝ)
    (hsum : Summable (actualHigherTailTerms ζ (2*(m+1)) j eps)) :
    actualHigherTail ζ (2*(m+1)) j eps =
      ∑' n : ℕ,‖iteratedDeriv j (coefficient (2*(n+m+2))) ((1+(eps:ℂ))*ζ)‖ := by
  have h := hsum.sum_add_tsum_nat_add (m+1)
  have hzero : (∑ n ∈ Finset.range (m+1),actualHigherTailTerms ζ (2*(m+1)) j eps n)=0 := by
    apply Finset.sum_eq_zero
    intro n hn
    have hn' := Finset.mem_range.mp hn
    simp only [actualHigherTailTerms,ite_eq_right (by omega : ¬ 2*(m+1)<2*(n+1))]
  rw [hzero,zero_add] at h
  unfold actualHigherTail
  rw [← h]
  apply tsum_congr
  intro n
  simp only [actualHigherTailTerms,ite_eq_left (by omega : 2*(m+1)<2*(n+(m+1)+1)),
    ofReal_add,ofReal_one]
  congr 3

theorem sqrt_log_bound_tendsto_zero {f : ℝ → ℂ} {C D eps0 : ℝ}
    (heps0 : 0 < eps0)
    (hbound : ∀ eps : ℝ, 0 < eps → eps < eps0 →
      ‖f eps‖ ≤ C+D*(1+|Real.log eps|)) :
    Tendsto (fun eps : ℝ => Real.sqrt eps • f eps) (𝓝[>] 0) (𝓝 0) := by
  have hs : Tendsto Real.sqrt (𝓝[>] (0:ℝ)) (𝓝 0) := by
    simpa using (Real.continuous_sqrt.tendsto (0:ℝ)).mono_left nhdsWithin_le_nhds
  have hb : Tendsto (fun eps : ℝ => C*Real.sqrt eps+
      D*(Real.sqrt eps*(1+|Real.log eps|))) (𝓝[>] 0) (𝓝 0) := by
    simpa using (hs.const_mul C).add (logarithmic_factor_times_sqrt_tendsto_zero.const_mul D)
  apply squeeze_zero_norm' (a := fun eps : ℝ => C*Real.sqrt eps+
    D*(Real.sqrt eps*(1+|Real.log eps|))) _ hb
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds heps0).filter_mono nhdsWithin_le_nhds] with eps he he0
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg eps)]
  calc
    _ ≤ Real.sqrt eps*(C+D*(1+|Real.log eps|)) :=
      mul_le_mul_of_nonneg_left (hbound eps he he0) (Real.sqrt_nonneg eps)
    _ = _ := by ring

/-- The complete actual infinite tail cannot cancel the first coefficient
when its concrete absolute bound and the finite complement have been proved. -/
theorem evenSeries_nonzero_radial_limit_of_obligations {ζ : ℂ} (hζ : ‖ζ‖=1)
    (m k : ℕ)
    (hfirst : PreferredFirstSingularityStatement ζ (2*(m+1)) k)
    (hlower : PreferredFiniteComplementStatement ζ m k)
    (htail : PreferredAbsoluteTailStatement ζ (2*(m+1)) k) :
    ∃ Λ : ℂ, Λ ≠ 0 ∧ Tendsto (fun eps : ℝ => Real.sqrt eps •
      iteratedDeriv k evenSeries ((1+(eps:ℂ))*ζ)) (𝓝[>] 0) (𝓝 Λ) := by
  obtain ⟨Λ,hΛ,hlim⟩ := hfirst
  obtain ⟨C,rC,_hC,hrC,hC⟩ := hlower
  obtain ⟨D,rD,_hD,hrD,hD⟩ := htail k le_rfl
  let f : ℝ → ℂ := fun eps => iteratedDeriv k evenSeries ((1+(eps:ℂ))*ζ)-
    iteratedDeriv k (coefficient (2*(m+1))) ((1+(eps:ℂ))*ζ)
  have hf : Tendsto (fun eps : ℝ => Real.sqrt eps • f eps) (𝓝[>] 0) (𝓝 0) := by
    apply sqrt_log_bound_tendsto_zero (C := C) (D := D) (lt_min hrC hrD)
    intro eps he he0
    have hce := hC eps he (he0.trans_le (min_le_left _ _))
    obtain ⟨hsumt,hdt⟩ := hD eps he (he0.trans_le (min_le_right _ _))
    have hs := radialPath_exterior hζ he
    have hsum := (even_coefficient_derivatives_absolutely_summable k hs).comp_injective
      (fun a b h => by change a+(m+1)=b+(m+1) at h; omega :
        Function.Injective (fun n : ℕ => n+(m+1)))
    have hnorm : ‖∑' n : ℕ,iteratedDeriv k (coefficient (2*(n+m+2))) ((1+(eps:ℂ))*ζ)‖ ≤
        actualHigherTail ζ (2*(m+1)) k eps := by
      rw [actualHigherTail_eq_shifted ζ m k eps hsumt]
      apply norm_tsum_le_tsum_norm
      convert hsum using 1
      funext n
      congr 3
    dsimp only [f]
    rw [evenSeries_derivative_split k m hs]
    have heq (a b c : ℂ) : a+b+c-b=a+c := by ring
    rw [heq]
    calc
      _ ≤ ‖∑ n ∈ Finset.range m,iteratedDeriv k (coefficient (2*(n+1))) ((1+(eps:ℂ))*ζ)‖+
          ‖∑' n : ℕ,iteratedDeriv k (coefficient (2*(n+m+2))) ((1+(eps:ℂ))*ζ)‖ := norm_add_le _ _
      _ ≤ C+D*(1+|Real.log eps|) :=
        add_le_add ((norm_sum_le _ _).trans hce) (hnorm.trans hdt)
  refine ⟨Λ,hΛ,?_⟩
  have h := hlim.add hf
  simp only [add_zero] at h
  convert h using 1
  funext eps
  dsimp only [f]
  rw [smul_sub]
  abel

theorem evenSeries_no_extension_of_obligations {ζ : ℂ} (hζ : ‖ζ‖=1)
    (m k : ℕ)
    (hfirst : PreferredFirstSingularityStatement ζ (2*(m+1)) k)
    (hlower : PreferredFiniteComplementStatement ζ m k)
    (htail : PreferredAbsoluteTailStatement ζ (2*(m+1)) k) :
    ¬ HasExteriorExtension evenSeries ζ := by
  obtain ⟨Λ,hΛ,hlim⟩ := evenSeries_nonzero_radial_limit_of_obligations hζ m k hfirst hlower htail
  exact no_extension_of_nonzero_radial_limit hζ hΛ k hlim

end
end IsingBulk.Preferred22
