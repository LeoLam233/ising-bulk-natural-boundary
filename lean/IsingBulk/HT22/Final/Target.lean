import IsingBulk.HT22.Final.NaturalBoundary
import IsingBulk.HT22.Transport.FieldNeighborhood.ActualAngularFrameJets
import IsingBulk.HT22.Transport.SharpCovarianceJets.Actual

/-! Exact public aggregate for the frozen F001 mathematics. The constructed
physical germs, full-site real input, complete infinite tail, exact FIRST
coefficient and quantitative original-source jets are exposed in its type.
This source theorem is distinct from post-freeze build/replay/audit acceptance. -/
namespace IsingBulk.HT22
noncomputable section
open IsingBulk.Preferred22 IsingBulk.HT22.Tail Geometry Set Metric Filter
open scoped Topology BigOperators ContDiff

def AngularFieldJetsStatement (b : PreferredBranchData) (M : ℝ) : Prop :=
  ∃ cap : ℝ, 0<cap ∧ cap<b.alpha ∧
      ∀ B : PreferredCoareaBump b, B.delta<cap →
      ∃ ε₀ τ₀ δB : ℝ, 0<ε₀ ∧ 0<τ₀ ∧ 0<δB ∧ δB<B.delta ∧
      ∀ j : ℕ, ∃ C : ℝ, 0<C ∧
      ∀ N : ℕ, 0<N → ∀ ε τ μ r : ℝ,
      0<ε → ε<ε₀ → 0≤τ → τ<τ₀ → 0<r → |μ|+r+ε≤M →
      ∀ θ : Fin N → ℝ,
      (∀ i, -δB≤θ i+b.b ∧ θ i≤B.delta) →
      (∀ i, μ-2*r≤θ i+b.b ∧ θ i+b.b≤μ+2*r) →
      ∀ i k : Fin N, (∀ a, θ i≤θ a ∧ θ a≤θ k) → r≤θ k-θ i →
      ∀ xs : List (Option (Fin N)), xs.length≤j → ∀ a : Fin N,
      ‖frameJet τ B.p B.m (fun t x => angularField τ B.p B.m t x a)
        xs (IsingBulk.Branch.radialParameter b.alpha ε) θ‖≤
        C*(N:ℝ)^(2*(j*j+4*j)+(2*j+2)+1)/(r/Real.sqrt (|μ|+r+ε))^(1+xs.length)

def SharpCovarianceJetsStatement (b : PreferredBranchData) (M : ℝ) : Prop :=
  ∃  cap : ℝ , 0 < cap  ∧ cap < b.alpha  ∧  ∀ B : PreferredCoareaBump b , B.delta < cap  → 
     ∃  ε₀ τ₀ δB ρ₀ c₀ : ℝ , 0 < ε₀  ∧ 0 < τ₀  ∧ 0 < δB  ∧ δB < B.delta  ∧ 0 < ρ₀  ∧ 0 < c₀  ∧ 
     ∀ m : ℕ ,  ∃ C : ℝ , 0 < C  ∧  ∀ N : ℕ , 0 < N  →  ∀ ε τ μ r : ℝ , 
    0 < ε  → ε < ε₀  → 0 ≤ τ  → τ < τ₀  → 0 < r  → |μ|+r+ε ≤ M  → 
     ∀ θ : Fin N → ℝ , ( ∀ i , -δB ≤ θ i+b.b  ∧ θ i ≤ B.delta)  → 
    ( ∀ i , μ-2*r ≤ θ i+b.b  ∧ θ i+b.b ≤ μ+2*r)  → 
     ∀ i k : Fin N , ( ∀ a , θ i ≤ θ a  ∧ θ a ≤ θ k)  → r ≤ θ k-θ i  → 
    let T := |μ|+r+ε
    let Δ := r/Real.sqrt T
    let x : SourcePoint N := (IsingBulk.Branch.radialParameter b.alpha ε , 
      Tail.sourceCoordinate τ B.p B.m (IsingBulk.Branch.radialParameter b.alpha ε) θ)
    ( ∀ y ∈ ball x (ρ₀*Δ/(N:ℝ)^2) , c₀*Real.sqrt T*Δ^2 ≤ ‖sourceCovariance y.1 y.2‖)  ∧ 
    ‖iteratedFDeriv ℂ m (fun z : SourcePoint N => sourceCovariance z.1 z.2) x‖ ≤ 
      C*(N:ℝ)^(2*m+2)*Real.sqrt T*Δ^2/Δ^m  ∧ 
    ‖iteratedFDeriv ℂ m (fun z : SourcePoint N => (sourceCovariance z.1 z.2)⁻¹) x‖ ≤ 
      C*(N:ℝ)^(2*m+2)/(Real.sqrt T*Δ^(m+2))  ∧ 
     ∀ a , ‖iteratedFDeriv ℂ m (fun z : SourcePoint N => SharpCovarianceJets.sourceCentered z.1 z.2 a) x‖ ≤ 
      C*(N:ℝ)^(2*m+2)*Real.sqrt T*Δ/Δ^m

structure HT22FullTarget : Prop where
  bulk_analytic : AnalyticOnNhd ℂ Physical.interiorBulk {s : ℂ | ‖s‖<1}
  bulk_boundary : ∀ z : ℂ,‖z‖=1 →
    ¬IsingBulk.HT.Final.HasInteriorExtension Physical.interiorBulk z
  susceptibility : ∀ J : ℝ,0<J →
    AnalyticOnNhd ℂ (Physical.physicalSusceptibility J) {s : ℂ | ‖s‖<1} ∧
    ∀ z : ℂ,‖z‖=1 → ¬IsingBulk.HT.Final.HasInteriorExtension (Physical.physicalSusceptibility J) z
  same_bulk_germ : EqOn Physical.interiorBulk IsingBulk.HT.Final.interiorFullBulk {s : ℂ | ‖s‖<1}
  same_susceptibility_germ : ∀ J : ℝ,
    EqOn (Physical.physicalSusceptibility J) (IsingBulk.HT.Final.interiorPhysicalSusceptibility J)
      {s : ℂ | ‖s‖<1}
  physical_input : ∀ corr : ℝ → PhysicalScope.LatticeSite → ℝ,
    PhysicalScope.PublishedRealHTSpinFormFactors corr → ∀ J : ℝ,0<J →
    ∀ s : ℝ,0<s → s<1 →
      Summable (fun v => |corr s v|) ∧
      (PhysicalScope.realBulk corr s:ℂ)=Physical.interiorBulk (s:ℂ) ∧
      (PhysicalScope.realSusceptibility J corr s:ℂ)=Physical.physicalSusceptibility J (s:ℂ) ∧
      PhysicalScope.realBulk corr s=1+∑' v : PhysicalScope.LatticeSite,
        if v=(0,0) then 0 else corr s v
  beta_coordinate : ∀ J s : ℝ,0<J → 0<s →
    0<Real.arsinh s/(2*J) ∧ Real.sinh (2*(Real.arsinh s/(2*J))*J)=s
  joint_lattice : ∀ t : ℝ,1<t →
    Summable (fun q : ℕ × (ℤ × ℤ) =>
      ‖IsingBulk.HT.Contour.physicalFullLatticeCoefficient (2*q.1+1) t q.2‖) ∧
    Physical.oddSeries (t:ℂ)=∑' v : ℤ × ℤ,∑' n : ℕ,
      IsingBulk.HT.Contour.physicalFullLatticeCoefficient (2*n+1) t v
  one_particle : ∀ t : ℝ,1<t → Physical.coefficient 1 (t:ℂ)=((t+t⁻¹-2)⁻¹:ℝ)
  absolute_tail : ∀ d : PreferredBranchData,
    ∃ ε₀ : ℝ,0<ε₀ ∧ ∀ p : ℕ,5≤p → Odd p → ∀ j : ℕ,
      j≤IsingBulk.HT.First.derivativeOrder p → ∃ C : ℝ,0<C ∧
      ∀ negative : Bool,∀ ε : ℝ,0<ε → ε<ε₀ →
      Summable (FullTail.coefficientMass negative p j d.alpha ε) ∧
      (∑' n,FullTail.coefficientMass negative p j d.alpha ε n)≤C*(1+|Real.log ε|)
  first_coefficient : ∀ p : ℕ,∀ _hp : p.Prime,∀ _hp5 : 5≤p,∀ a : ℤ,
    Arithmetic.PrimeIndex p a →
    equalAngleLeadingCoefficient p (IsingBulk.PrimeFamily.angle p a)≠0 ∧
    Asymptotics.IsLittleO (𝓝[>] (0:ℝ))
      (fun ε => iteratedDeriv (IsingBulk.HT.First.derivativeOrder p) (Physical.signedCoefficient false p)
        (IsingBulk.Branch.radialParameter (IsingBulk.PrimeFamily.angle p a) ε)-
        (ε:ℂ)⁻¹*equalAngleLeadingCoefficient p (IsingBulk.PrimeFamily.angle p a))
      (fun ε => (ε:ℂ)⁻¹)
  prime_full_limit : ∀ p : ℕ,∀ hp : p.Prime,∀ hp5 : 5≤p,∀ a : ℤ,
    ∀ ha : Arithmetic.PrimeIndex p a,
    LocalLimit.physicalCriticalLeadingCoefficient p (IsingBulk.PrimeFamily.angle p a)≠0 ∧
    Tendsto (fun ε : ℝ => ε • iteratedDeriv (IsingBulk.HT.First.derivativeOrder p)
      (Physical.signedOddSeries (Arithmetic.negativeSide (IsingBulk.PrimeFamily.angle p a)))
      (IsingBulk.Branch.radialParameter (Arithmetic.primeBranchData hp hp5 ha).alpha ε)) (𝓝[>] 0)
      (𝓝 (LocalLimit.physicalCriticalLeadingCoefficient p (IsingBulk.PrimeFamily.angle p a)))
  angular_jets : ∀ b : PreferredBranchData,∀ M : ℝ,0<M → AngularFieldJetsStatement b M
  sharp_covariance_jets : ∀ b : PreferredBranchData,∀ M : ℝ,0<M → SharpCovarianceJetsStatement b M

/-- Complete source-level F001 theorem. No analytic-tail, FIRST, continuation,
or natural-boundary hypothesis is admitted as an input. -/
theorem ht22_full_target : HT22FullTarget where
  bulk_analytic := Final.f001_natural_boundary.1
  bulk_boundary := Final.f001_natural_boundary.2.1
  susceptibility := Final.f001_natural_boundary.2.2
  same_bulk_germ := Physical.interiorBulk_eqOn_existing
  same_susceptibility_germ := Physical.physicalSusceptibility_eqOn_existing
  physical_input := fun _ hphys _ hJ => (Final.f001_full_lattice_physical hphys hJ).1
  beta_coordinate := fun _ _ hJ hs => PhysicalScope.real_temperature_coordinate hJ hs
  joint_lattice := fun _ ht => ⟨Physical.full_odd_lattice_norm_summable ht,Physical.oddSeries_real_eq_siteFirst ht⟩
  one_particle := fun _ ht => Physical.coefficient_one_real ht
  absolute_tail := FullTail.actual_absolute_tail
  first_coefficient := fun _ hp hp5 _ ha => Finite.actual_original_prime_first_asymptotic hp hp5 ha
  prime_full_limit := fun _ hp hp5 _ ha => Final.actual_prime_full_limit hp hp5 ha
  angular_jets := fun b M hM => actual_angular_field_uniform_frame_budget b M hM
  sharp_covariance_jets := fun b M hM => SharpCovarianceJets.actual_sharp_covariance_jets b M hM

end
end IsingBulk.HT22
