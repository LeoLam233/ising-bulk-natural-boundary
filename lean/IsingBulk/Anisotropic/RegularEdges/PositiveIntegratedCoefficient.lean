import IsingBulk.Anisotropic.RegularEdges.CenteredAngularJets
import IsingBulk.Anisotropic.RegularEdges.AngularNumeratorBridge
import IsingBulk.Anisotropic.RegularEdges.IntegratedJets
import IsingBulk.Anisotropic.NegativeDominance.NormalizedAngularMeasure

noncomputable section
open MeasureTheory Set Filter IsingBulk.First IsingBulk.HT.Contour
open scoped Topology BigOperators
namespace IsingBulk.Anisotropic.RegularEdges

theorem complexAngularDensity_eq_edgeFullIntegrand {N : ℕ} (hN : 0<N)
    {lam b : ℝ} {B S : ℂ → ℂ} {z u : ℂ}
    (hz : z∉spectralSet lam) (hs : spectralS z≠0)
    (hB : B u=spectralT lam z/spectralS z) (hS : S u=spectralS z)
    (he : edgeMapV lam 1 z=(b:ℂ)+u) (hu : 0<u.im) (hBi : 0<(B u).im)
    (q : Fin N → ℝ) :
    complexAngularDensity lam z (fun i => (q i:ℂ))=edgeFullIntegrand b B S u q := by
  have hd := one_sub_coordinateProduct_ne_zero hN
    (fun i => (transferRoot_bounds hz hs (q i)).2)
  simp_rw [transferRoot_eq_edgeParamRoot hB he hu hBi] at hd
  change 1-∏ i,edgeParamRoot b B u (q i)≠0 at hd
  unfold complexAngularDensity
  rw [complexAngularWeight_eq_edgeNumerator hB hS he hu hBi]
  simp_rw [transferRoot_eq_edgeParamRoot hB he hu hBi]
  unfold edgeFullIntegrand edgeRootProduct
  field_simp [hd]
  ring

theorem unscaledAngularCoefficient_edge_iteratedDeriv (n j : ℕ)
    {lam b : ℝ} {U : Set ℂ} {zeta B S : ℂ → ℂ} (hU : IsOpen U)
    (ha : AnalyticOnNhd ℂ zeta U) (hz : ∀ u∈U, zeta u∉spectralSet lam)
    (hs : ∀ u∈U, spectralS (zeta u)≠0)
    (hB : ∀u∈U, B u=spectralT lam (zeta u)/spectralS (zeta u))
    (hS : ∀u∈U, S u=spectralS (zeta u))
    (he : ∀u∈U, edgeMapV lam 1 (zeta u)=(b:ℂ)+u)
    (huIm : ∀u∈U, 0<u.im) (hBi : ∀u∈U, 0<(B u).im)
    {u : ℂ} (hu : u∈U) :
    iteratedDeriv j (fun v => unscaledAngularCoefficient n lam (zeta v)) u =
      ((n+1).factorial:ℂ)⁻¹ * ∫ q : Fin n → ℝ,
        iteratedDeriv j (fun v => edgeFullIntegrand b B S v (centeredFullAngles n q)) u
          ∂Measure.pi (fun _ => edgeAngleMeasure) := by
  rw [unscaledAngularCoefficient_comp_iteratedDeriv n j hU ha hz hs hu,mul_assoc,
    ←edgeAngleMeasure_integral_eq]
  congr 1
  apply integral_congr_ae
  apply Eventually.of_forall
  intro q
  apply Filter.EventuallyEq.iteratedDeriv_eq
  filter_upwards [hU.mem_nhds hu] with v hv
  rw [←complexAngularDensity_wrapAngle lam (zeta v) (physicalDependentAngles n q)]
  exact complexAngularDensity_eq_edgeFullIntegrand (by omega) (hz v hv) (hs v hv)
    (hB v hv) (hS v hv) (he v hv) (huIm v hv) (hBi v hv) _

end IsingBulk.Anisotropic.RegularEdges
