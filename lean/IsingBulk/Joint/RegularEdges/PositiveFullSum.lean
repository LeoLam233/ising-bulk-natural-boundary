import IsingBulk.Joint.RegularEdges.FullSeriesJets
import IsingBulk.Anisotropic.RegularEdges.LeadingJetTransfer
import IsingBulk.Anisotropic.RegularEdges.LeadingSeries
import IsingBulk.Anisotropic.RegularEdges.LeadingNonextension
import IsingBulk.Anisotropic.RegularEdges.LeadingArithmetic
import IsingBulk.Anisotropic.RegularEdges.PhasePrime

/-! # Positive-edge obstruction of the actual whole parity sums
These theorems quantify over arbitrary holomorphic anisotropies. All infinitely
many competing particle indices and all fixed derivatives are discharged by the
constructed integral estimates, not by a supplied whole-sum hypothesis.
-/
namespace IsingBulk.Joint.RegularEdges
noncomputable section
open IsingBulk.First IsingBulk.Tail IsingBulk.Anisotropic
open IsingBulk.Anisotropic.RegularEdges Set Filter MeasureTheory
open scoped Topology

section Curve
variable {b : ℝ} {B S : ℂ → ℂ} {U : Set ℂ}
variable (hb : |b| < 1) (hB0 : 0 < (B 0).im) (hBa0 : AnalyticAt ℂ B 0)
  (hSa0 : AnalyticAt ℂ S 0) (hS0 : S 0 ≠ 0)
  (hU : IsOpen U) (hBa : AnalyticOnNhd ℂ B U) (hSa : AnalyticOnNhd ℂ S U)
  (hu : ∀ u ∈ U, 0 < u.im) (hBi : ∀ u ∈ U, 0 < (B u).im) (hS : ∀ u ∈ U, S u ≠ 0)
  (hin : ∀ᶠ t : ℝ in 𝓝[>] 0, Complex.I*(t:ℂ)^2 ∈ U)
include hb hB0 hBa0 hSa0 hS0 hU hBa hSa hu hBi hS hin

/-- The unique first resonant particle survives the entire selected series.
The only selection premises are explicit integer arithmetic and root resonance. -/
theorem paritySeries_first_limit {e p j a : ℕ} (ha : 0 < a) (hp : p < j+2)
    (hres : continuedRoot (b:ℂ)^(2*p+e+1)=1)
    (hlower : ∀ i < p, continuedRoot (b:ℂ)^(2*i+e+1)≠1)
    (hhigher : ∀ i : ℕ, p < i → 1 ≤ 2*i+e ∧ 2*(j+1) ≤ (2*i+e+1)*(2*i+e))
    (hbalance : (2*p+e)+a+(2*p+e+1)*(2*p+e)=2*(j+1))
    (hmajorant : Integrable (@shapeMajorant (2*p+e) j)) :
    Tendsto (fun t : ℝ => (t^a) • iteratedDeriv j
      (paritySeries e b B S) (Complex.I*(t:ℂ)^2)) (𝓝[>] 0)
      (𝓝 (edgeCoefficientLeading (2*p+e) j b B S)) := by
  have htend : Tendsto (fun t : ℝ => Complex.I*(t:ℂ)^2) (𝓝[>] 0) (𝓝 0) := by
    simpa using! ((by fun_prop : Continuous (fun t : ℝ => Complex.I*(t:ℂ)^2)).tendsto 0).mono_left nhdsWithin_le_nhds
  obtain ⟨δ,hδ,hjets⟩ := paritySeries_local_jets hb hB0 hBa0 hSa0 hS0 hU hBa hSa hu hBi hS
  obtain ⟨η,G,hη,hG,_,hbound⟩ := angularCoefficient_summable_jet_majorants
    hb hB0 hBa0 hSa0 hS0 hU hBa hSa hu hBi hS j
  have hJet (n : ℕ) : ∀ k u, u ∈ U →
      iteratedDeriv k (angularCoefficient n b B S) u =
        edgeCoefficientNormalization n * edgeFullDerivativeIntegral (n := n) b B S k u :=
    fun k u huU => angularCoefficient_iteratedDeriv hU hBa hSa hu hBi hS n k huU
  apply scaled_series_first_limit ha hp
    (f := fun i t => iteratedDeriv j (angularCoefficient (2*i+e) b B S) (Complex.I*(t:ℂ)^2))
  · filter_upwards [hin,htend.eventually (Metric.ball_mem_nhds _ hδ)] with t ht htd
    exact (hjets e _ ht (by simpa using htd)).2 j
  · intro i hi
    by_cases hip : i=p
    · subst i
      simp only [ite_true]
      exact coefficient_scaled_limit_of_full_jets (hJet _) hin
        (edgeFullDerivativeIntegral_leading_limit ha hbalance hmajorant hb hBa0 hB0 hSa0 hS0 hres)
    · simp only [hip,ite_false]
      have hz : Tendsto (fun t : ℝ => (t^a) •
          edgeFullDerivativeIntegral (n := 2*i+e) b B S j (Complex.I*(t:ℂ)^2))
          (𝓝[>] 0) (𝓝 0) := by
        apply bounded_jet_scaled_zero ha
        rcases lt_or_gt_of_ne hip with hlt | hgt
        · obtain ⟨C,_,hC⟩ := edgeFullDerivativeIntegral_nonresonant_bounded hb hBa0 hB0 hSa0 hS0 (hlower i hlt) j
          exact ⟨C,htend.eventually hC⟩
        · obtain ⟨C,_,hC⟩ := edgeFullDerivativeIntegral_higher_bounded
            (hhigher i hgt).1 (hhigher i hgt).2 hb hBa0 hB0 hSa0 hS0
          exact ⟨C,hC⟩
      simpa only [mul_zero] using coefficient_scaled_limit_of_full_jets (hJet _) hin hz
  · exact hG.comp_injective (i := fun i : ℕ => 2*i+1+e) (by intro x y h; dsimp at h; omega)
  · filter_upwards [hin,htend.eventually (Metric.ball_mem_nhds _ hη)] with t ht htd i
    have h := hbound _ ht (by simpa using htd) (2*i+1+e)
    change ‖iteratedDeriv j (angularCoefficient (2*(i+(j+2))+e) b B S)
      (Complex.I*(t:ℂ)^2)‖ ≤ G (2*i+1+e)
    rw [show 2*(i+(j+2))+e = 2*j+3+(2*i+1+e) by omega]
    exact h

/-- The complete odd series, with every higher odd order retained. -/
theorem oddSeries_first_singularity {q j : ℕ} (hq : 1 ≤ q)
    (hcritical : 2*j+1=(2*q+1)^2) (hres : continuedRoot (b:ℂ)^(2*q+1)=1)
    (hearly : ∀ i < q, continuedRoot (b:ℂ)^(2*i+1)≠1) :
    let C := edgeCoefficientLeading (2*q) j b B S
    C≠0 ∧ Tendsto (fun t : ℝ => (t^2) • iteratedDeriv j
      (paritySeries 0 b B S) (Complex.I*(t:ℂ)^2)) (𝓝[>] 0) (𝓝 C) ∧
      ¬HasDomainExtension U (paritySeries 0 b B S) 0 := by
  dsimp only
  obtain ⟨hj,hdegree⟩ := odd_first_degree hq hcritical
  have hfull : edgeFullLeadingCoefficient (2*q) j b B S≠0 := by
    simpa [Nat.sub_add_cancel hj] using
      (odd_edge_full_leading_amplitude (by omega : 1≤2*q) hdegree hb hBa0 hB0 hSa0 hS0 hres).1
  have hC : edgeCoefficientLeading (2*q) j b B S≠0 :=
    mul_ne_zero (edgeCoefficientNormalization_ne_zero _) hfull
  have hlim := paritySeries_first_limit hb hB0 hBa0 hSa0 hS0 hU hBa hSa hu hBi hS hin
    (e := 0) (p := q) (j := j) (a := 2) (by omega) (by nlinarith : q < j+2)
    (by simpa using hres) (by simpa using hearly)
    (fun i hi => by simpa using odd_higher_degree hcritical hi)
    (by simpa using odd_first_balance hcritical) (by simpa using odd_first_majorant_integrable hq hcritical)
  refine ⟨hC,by simpa using hlim,?_⟩
  exact no_domain_extension_of_scaled_jet_limit hU (a := 2) (by omega) hC hin (by simpa using hlim)

/-- The complete nonzero even series, including its whole differentiated tail. -/
theorem evenSeries_first_singularity {q j : ℕ}
    (hcritical : 2*(j+1)=(2*q+2)^2) (hres : continuedRoot (b:ℂ)^(2*q+2)=1)
    (hearly : ∀ i < q, continuedRoot (b:ℂ)^(2*i+2)≠1) :
    let C := edgeCoefficientLeading (2*q+1) j b B S
    C≠0 ∧ Tendsto (fun t : ℝ => t • iteratedDeriv j
      (paritySeries 1 b B S) (Complex.I*(t:ℂ)^2)) (𝓝[>] 0) (𝓝 C) ∧
      ¬HasDomainExtension U (paritySeries 1 b B S) 0 := by
  dsimp only
  have hfull : edgeFullLeadingCoefficient (2*q+1) j b B S≠0 :=
    (even_edge_full_leading_amplitude (by omega : 1≤2*q+1) (even_first_degree hcritical)
      hb hBa0 hB0 hSa0 hS0 (by simpa only [Nat.add_assoc] using hres)).1
  have hC : edgeCoefficientLeading (2*q+1) j b B S≠0 :=
    mul_ne_zero (edgeCoefficientNormalization_ne_zero _) hfull
  have hlim := paritySeries_first_limit hb hB0 hBa0 hSa0 hS0 hU hBa hSa hu hBi hS hin
    (e := 1) (p := q) (j := j) (a := 1) (by omega) (by nlinarith : q < j+2)
    (by simpa only [Nat.add_assoc] using hres) (by simpa only [Nat.add_assoc] using hearly)
    (fun i hi => even_higher_degree hcritical hi)
    (even_first_balance hcritical) (even_first_majorant_integrable hcritical)
  refine ⟨hC,by simpa using hlim,?_⟩
  exact no_domain_extension_of_scaled_jet_limit hU (a := 1) (by omega) hC hin hlim

/-- The dense selected prime phases obstruct both complete parity series for
every variable-anisotropy curve satisfying the literal local branch conditions. -/
theorem prime_paritySeries_no_extension (hprime : b ∈ primePhaseCosines) :
    ¬HasDomainExtension U (paritySeries 0 b B S) 0 ∧
    ¬HasDomainExtension U (paritySeries 1 b B S) 0 := by
  constructor
  · obtain ⟨q,j,hq,hcritical,hres,hearly⟩ := primeCosine_first_odd hprime
    exact (oddSeries_first_singularity hb hB0 hBa0 hSa0 hS0 hU hBa hSa hu hBi hS hin
      hq hcritical hres hearly).2.2
  · obtain ⟨q,j,hcritical,hres,hearly⟩ := primeCosine_first_even hprime
    exact (evenSeries_first_singularity hb hB0 hBa0 hSa0 hS0 hU hBa hSa hu hBi hS hin
      hcritical hres hearly).2.2

end Curve
end
end IsingBulk.Joint.RegularEdges
