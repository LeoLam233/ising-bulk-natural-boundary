import IsingBulk.Joint.RegularEdges.FullDifferentiatedTail
import IsingBulk.Anisotropic.FormFactors.AnalyticSeriesJets

/-! # Actual parity series and all derivatives on the physical side
The full series is formed from the complete angular integrals. A summable
all-index envelope is derived, and analytic differentiation is internal.
-/
namespace IsingBulk.Joint.RegularEdges
noncomputable section
open IsingBulk.Anisotropic.RegularEdges IsingBulk.Anisotropic.FormFactors Set Filter Metric
open scoped Topology BigOperators

/-- `e=0` is all odd particles; `e=1` is all nonzero even particles. -/
def paritySeries (e : ℕ) (b : ℝ) (B S : ℂ → ℂ) (u : ℂ) : ℂ :=
  ∑' i, angularCoefficient (2*i+e) b B S u

theorem paritySeries_local_jets {b : ℝ} {B S : ℂ → ℂ} {U : Set ℂ}
    (hb : |b| < 1) (hB0 : 0 < (B 0).im) (hBa0 : AnalyticAt ℂ B 0)
    (hSa0 : AnalyticAt ℂ S 0) (hS0 : S 0 ≠ 0)
    (hU : IsOpen U) (hBa : AnalyticOnNhd ℂ B U) (hSa : AnalyticOnNhd ℂ S U)
    (hu : ∀ u ∈ U, 0 < u.im) (hBi : ∀ u ∈ U, 0 < (B u).im) (hS : ∀ u ∈ U, S u ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ e : ℕ, ∀ u ∈ U, ‖u‖ < δ →
      AnalyticAt ℂ (paritySeries e b B S) u ∧
      ∀ j : ℕ, HasSum (fun i => iteratedDeriv j (angularCoefficient (2*i+e) b B S) u)
        (iteratedDeriv j (paritySeries e b B S) u) := by
  obtain ⟨δ,G,hδ,hG,_,hbound⟩ := angularCoefficient_summable_jet_majorants
    hb hB0 hBa0 hSa0 hS0 hU hBa hSa hu hBi hS 0
  refine ⟨δ,hδ,?_⟩
  intro e u huU hud
  let H : ℕ → ℝ := fun n => if n < 3 then ‖angularCoefficient n b B S u‖+1 else G (n-3)
  have hH : Summable H := by
    apply (summable_nat_add_iff 3).mp
    simpa [H] using hG
  have hlow : ∀ᶠ v in 𝓝 u, ∀ n ∈ Finset.range 3,
      ‖angularCoefficient n b B S v‖ ≤ ‖angularCoefficient n b B S u‖+1 := by
    rw [Finset.eventually_all]
    intro n _
    exact ((angularCoefficient_analyticAt hU hBa hSa hu hBi hS n huU).continuousAt.norm.eventually_lt
      continuousAt_const (by linarith)).mono (fun _ h => h.le)
  have hev : ∀ᶠ v in 𝓝 u, v ∈ U ∧ ‖v‖ < δ ∧
      ∀ n, ‖angularCoefficient n b B S v‖ ≤ H n := by
    filter_upwards [hU.mem_nhds huU,((continuous_norm).isOpen_preimage _ isOpen_Iio).mem_nhds hud,hlow]
      with v hv hvd hvlow
    refine ⟨hv,hvd,?_⟩
    intro n
    dsimp [H]
    split_ifs with hn
    · exact hvlow n (Finset.mem_range.mpr hn)
    · have ht := hbound v hv hvd (n-3)
      have he : 2*0+3+(n-3)=n := by omega
      simpa only [he,iteratedDeriv_zero] using ht
  obtain ⟨V,hVsub,hVo,huV⟩ := _root_.mem_nhds_iff.mp hev
  have hsub : V ⊆ U := fun v hv => (hVsub hv).1
  have hcoef (n : ℕ) : AnalyticOnNhd ℂ (angularCoefficient n b B S) V :=
    fun v hv => angularCoefficient_analyticAt hU hBa hSa hu hBi hS n (hsub hv)
  have hsel : Summable (fun i => H (2*i+e)) := hH.comp_injective (by intro a b h; dsimp at h; omega)
  have hnorm (i : ℕ) (v : ℂ) (hv : v∈V) : ‖angularCoefficient (2*i+e) b B S v‖ ≤ H (2*i+e) :=
    (hVsub hv).2.2 _
  constructor
  · exact (Complex.differentiableOn_tsum_of_summable_norm hsel
      (fun i v hv => (hcoef (2*i+e) v hv).differentiableAt.differentiableWithinAt)
      hVo hnorm).analyticOnNhd hVo u huV
  · intro j
    exact hasSum_iteratedDeriv_of_summable_envelope hVo (fun i => hcoef (2*i+e)) hsel hnorm j huV

end
end IsingBulk.Joint.RegularEdges
