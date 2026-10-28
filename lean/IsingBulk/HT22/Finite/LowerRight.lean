import IsingBulk.HT22.Finite.LocalizedAssembly
import IsingBulk.HT22.Geometry.LowerFiniteDecomposition
import IsingBulk.HT22.Arithmetic.BranchCharts
namespace IsingBulk.HT22.Finite
noncomputable section
open Set Filter IsingBulk.Preferred22 IsingBulk.PrimeFamily Arithmetic Geometry
open Physical Physical.FiniteAssembly
open scoped Topology BigOperators ContDiff
set_option backward.isDefEq.respectTransparency false

theorem prime_lower_right_bound_of_separated_remainder {p : ℕ} (hp : p.Prime) (hp5 : 5≤p)
    {a : ℤ} (ha : PrimeIndex p a) :
    ∃ g : ℝ,0<g ∧ ∀ B : PreferredCoareaBump (primeBranchData hp hp5 ha),
    ∀ τ : ℝ,0≤τ → ∀ δ : ℝ,δ≤g/4 → ∀ rcut : ℝ → ℝ,
    PreferredRightCutoffData (primeBranchData hp hp5 ha) B δ rcut →
    ∀ n : ℕ,Odd (n+1) → n+1<p → ∀ j : ℕ,
    (∀ rem : (Fin n → ℝ) → ℝ,ContDiff ℝ ∞ rem →
      (∃ R : ℝ,0<R ∧ ∀ θ∈signedRightRegion (constraintAngle (negativeSide (angle p a)))
        (primeBranchData hp hp5 ha) B δ,rem θ≠0 →
        R<preferredAngularDiameter (preferredLiftedAngles B.delta
          (constrainedAtTotal (constraintAngle (negativeSide (angle p a))) θ))) →
      ∃ C e : ℝ,0<C ∧ 0<e ∧ ∀ ε : ℝ,0<ε → ε<e →
        ‖iteratedDeriv j (localizedRightIntegral (negativeSide (angle p a)) n τ B.p B.m rcut rem)
          (IsingBulk.Branch.radialParameter (primeBranchData hp hp5 ha).alpha ε)‖≤C*(1+|Real.log ε|)) →
    ∃ C e : ℝ,0<C ∧ 0<e ∧ ∀ ε : ℝ,0<ε → ε<e →
      ‖iteratedDeriv j (rightPopulationIntegral (negativeSide (angle p a)) n τ preferredPopulationCutoff B.p B.m rcut)
        (IsingBulk.Branch.radialParameter (primeBranchData hp hp5 ha).alpha ε)‖≤C*(1+|Real.log ε|) := by
  let d := primeBranchData hp hp5 ha
  let negative := negativeSide (angle p a)
  obtain ⟨g,hg,hpartition⟩ := lower_signed_finite_decomposition hp hp5 ha d negative
    (primeBranchData_cos hp hp5 ha)
  refine ⟨g,hg,?_⟩
  intro B τ hτ δ hδ rcut hcut n hn hnp j hfar
  obtain ⟨P,rem,R,hR,hrem,hP,hid,hsep,hlocal⟩ := hpartition B τ hτ n hn hnp δ hcut.2.1 hδ
  apply right_log_bound_of_local_partition negative n d B hτ rcut hcut.2.2.1
    P rem (fun ψ hψ => (hP ψ hψ).1.continuous) hrem.continuous hid j
  · intro ψ hψ
    apply localized_bound_from_lifted negative n d B τ rcut hcut.2.2.2.1 ψ j
    exact hlocal ψ hψ (Physical.FiniteAssembly.rightContourWeight n τ B.p B.m rcut)
      (rightContourWeight_continuous n d B τ rcut hcut.2.2.1) j
  · exact hfar rem hrem ⟨R,hR,hsep⟩
end
end IsingBulk.HT22.Finite
