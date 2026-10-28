import IsingBulk.HT22.Finite.CriticalLimit
import IsingBulk.HT22.Finite.FirstAssembly
import IsingBulk.HT22.Finite.LocalizedAssembly
import IsingBulk.HT22.Geometry.FirstFiniteDecomposition
namespace IsingBulk.HT22.Finite
noncomputable section
open Complex Set Filter Metric IsingBulk.First IsingBulk.Branch IsingBulk.HT.First
open IsingBulk.PrimeFamily Arithmetic LocalLimit Geometry IsingBulk.Preferred22
open Physical Physical.FiniteAssembly
open scoped Topology ContDiff
set_option backward.isDefEq.respectTransparency false

theorem prime_right_limit_of_separated_remainder {p : ℕ} (hp : p.Prime) (hp5 : 5≤p)
    {a : ℤ} (ha : PrimeIndex p a) :
    ∃ g : ℝ,0<g ∧ ∀ B : PreferredCoareaBump (primeBranchData hp hp5 ha),
      ∀ τ : ℝ,0≤τ → ∀ δ : ℝ,δ≤g/4 → ∀ rcut : ℝ → ℝ,
      PreferredRightCutoffData (primeBranchData hp hp5 ha) B δ rcut →
      (∀ rem : (Fin (p-1) → ℝ) → ℝ,ContDiff ℝ ∞ rem →
        (∃ r : ℝ,0<r ∧ ∀ θ∈signedRightRegion (constraintAngle (negativeSide (angle p a)))
          (primeBranchData hp hp5 ha) B δ,rem θ≠0 →
          r<preferredAngularDiameter (preferredLiftedAngles B.delta
            (constrainedAtTotal (constraintAngle (negativeSide (angle p a))) θ))) →
        ∃ C e : ℝ,0<C ∧ 0<e ∧ ∀ ε : ℝ,0<ε → ε<e →
          ‖iteratedDeriv (derivativeOrder p)
            (localizedRightIntegral (negativeSide (angle p a)) (p-1) τ B.p B.m rcut rem)
            (radialParameter (primeBranchData hp hp5 ha).alpha ε)‖≤C*(1+|Real.log ε|)) →
      Tendsto (fun ε : ℝ => ε • iteratedDeriv (derivativeOrder p)
        (rightPopulationIntegral (negativeSide (angle p a)) (p-1) τ preferredPopulationCutoff B.p B.m rcut)
        (radialParameter (primeBranchData hp hp5 ha).alpha ε))
        (𝓝[>] 0) (𝓝 ((1/2:ℂ)*physicalCriticalLeadingCoefficient p (angle p a))) := by
  let d := primeBranchData hp hp5 ha
  let negative := negativeSide (angle p a)
  obtain ⟨g,hg,hpartition⟩ := first_signed_finite_decomposition hp hp5 ha d negative
    (primeBranchData_cos hp hp5 ha)
  refine ⟨g,hg,?_⟩
  intro B τ hτ δ hδ rcut hcut hfar
  have he : p-1+1=p := by omega
  obtain ⟨l,hl⟩ := primeBranchData_critical_mean hp hp5 ha
  obtain ⟨R,hR,hlimit⟩ := prime_actual_critical_cutoff_limit hp hp5 ha B δ rcut hcut
  obtain ⟨χ,P,rem,r,hr,hχ,hχcompact,hχrange,hχsupport,hχone,hrem,hP,hid,hsep,_hgerm,hbound⟩ :=
    hpartition B τ hτ (p-1) he δ hcut.2.1 hδ l (by simpa only [he] using hl) R hR
  have hχ0 : χ (fun _ => -d.alpha)=1 := hχone.self_of_nhds
  have hχsupp : ∀u,χ u≠0 → ‖u-(fun _ => -d.alpha)‖<R := by
    intro u hu
    exact (mem_ball.mp (hχsupport (subset_tsupport χ hu)))
  apply right_limit_of_critical_partition negative (p-1) d B hτ rcut hcut.2.2.1
    χ P rem hχ.continuous (fun ψ hψ => (hP ψ hψ).1.continuous) hrem.continuous hid
  · exact hlimit χ hχ.continuous hχ0 hχrange hχsupp τ
  · intro ψ hψ
    apply localized_bound_from_lifted negative (p-1) d B τ rcut hcut.2.2.2.1 ψ
    exact hbound ψ hψ (Physical.FiniteAssembly.rightContourWeight (p-1) τ B.p B.m rcut)
      (rightContourWeight_continuous (p-1) d B τ rcut hcut.2.2.1) _
  · exact hfar rem hrem ⟨r,hr,hsep⟩

end
end IsingBulk.HT22.Finite
