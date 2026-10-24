import IsingBulk.Anisotropic.PhysicalField.FiniteSpinLaw
import IsingBulk.Anisotropic.PhysicalField.ThermodynamicSqueeze
import IsingBulk.Anisotropic.FormFactors.PublishedRealInput
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

namespace IsingBulk.Anisotropic.PhysicalField
noncomputable section
open Set Filter FormFactors
open scoped Topology BigOperators

/-- Concrete real Gibbs-field data used in the manuscript's squeeze argument.
No susceptibility derivative, summability, or complex conclusion is a field.
These conditions must be attached to the physical Gibbs states; this structure
alone is not asserted to follow from the spin/form-factor representation. -/
structure GibbsFieldConditions (β : ℝ) (c : LatticeSite → ℝ) (m : ℝ → ℝ) where
  enumeration : ℕ ≃ LatticeSite
  localLaw : ∀ n, FiniteSpinLaw n
  volumeLaw : ∀ n, FiniteSpinLaw n
  local_center : ∀ n, (localLaw n).centerMean=m 0
  local_covariance : ∀ n (i : Fin n), (localLaw n).siteCovariance i=c (enumeration i.val)
  field_monotonicity : ∀ n h, 0<h → (localLaw n).magnetization β h≤m h
  covariance_nonnegative : ∀ v, 0≤c v
  pinned_covariance : ∀ n (i : Fin n), (volumeLaw n).siteCovariance i≤c (enumeration i.val)
  ghs_concavity : ∀ n, ConcaveOn ℝ (Ici 0) ((volumeLaw n).magnetization β)
  thermodynamic_limit : ∀ h, 0≤h →
    Tendsto (fun n => (volumeLaw n).magnetization β h) atTop (𝓝 (m h))

theorem enumerated_covariance_sum_tendsto (e : ℕ ≃ LatticeSite)
    {c : LatticeSite → ℝ} (hc : Summable c) :
    Tendsto (fun n => ∑ i : Fin n, c (e i.val)) atTop (𝓝 (∑' v, c v)) := by
  have hh := (hc.comp_injective e.injective).hasSum.tendsto_sum_nat
  simp only [Function.comp_def] at hh
  rw [e.tsum_eq] at hh
  have heq : (fun n => ∑ i : Fin n, c (e i.val)) =
      (fun n => ∑ i ∈ Finset.range n, c (e i)) := by
    funext n
    exact Fin.sum_univ_eq_sum_range (fun i => c (e i)) n
  rw [heq]
  exact hh

theorem field_response_of_gibbs_conditions {β : ℝ} (hβ : 0≤β)
    {c : LatticeSite → ℝ} {m : ℝ → ℝ}
    (G : GibbsFieldConditions β c m) (hc : Summable c) :
    HasDerivWithinAt m (β*∑' v, c v) (Ioi 0) 0 := by
  let d : ℕ → ℝ := fun n => β*∑ i : Fin n, c (G.enumeration i.val)
  apply thermodynamic_uniform_field_derivative m
    (fun n => (G.localLaw n).magnetization β)
    (fun n => (G.volumeLaw n).magnetization β)
    d (fun n => β*∑ i, (G.volumeLaw n).siteCovariance i) _
  · intro n
    rw [FiniteSpinLaw.magnetization_zero,G.local_center]
  · exact G.field_monotonicity
  · intro n
    simpa only [G.local_covariance] using (G.localLaw n).magnetization_derivative β
  · exact tendsto_const_nhds.mul (enumerated_covariance_sum_tendsto G.enumeration hc)
  · exact G.ghs_concavity
  · intro n
    exact (G.volumeLaw n).magnetization_derivative β
  · intro n
    apply mul_le_mul_of_nonneg_left _ hβ
    calc
      (∑ i, (G.volumeLaw n).siteCovariance i) ≤ ∑ i : Fin n, c (G.enumeration i.val) :=
        Finset.sum_le_sum (fun i _ => G.pinned_covariance n i)
      _ ≤ ∑' v, c v := by
        have heq : (∑ i : Fin n, c (G.enumeration i.val)) =
            ∑ i ∈ Finset.range n, c (G.enumeration i) :=
          Fin.sum_univ_eq_sum_range (fun i => c (G.enumeration i)) n
        rw [heq,← G.enumeration.tsum_eq]
        exact (hc.comp_injective G.enumeration.injective).sum_le_tsum _
          (fun i _ => G.covariance_nonnegative (G.enumeration i))
  · exact G.thermodynamic_limit

end
end IsingBulk.Anisotropic.PhysicalField
