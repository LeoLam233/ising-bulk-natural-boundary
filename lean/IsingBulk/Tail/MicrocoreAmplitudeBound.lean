import IsingBulk.Tail.MicrocoreAmplitudeJets

/-! Actual microcore amplitude finite jets at every N from common scalar
neighborhoods. The explicit product budget has exponential O_J(N²) size. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Branch IsingBulk.Jets Filter
open scoped BigOperators Topology

 structure MicroFactorBounds {N : ℕ} (z : ℂ × (Fin N → ℂ)) (J : ℕ) (C : ℝ) : Prop where
  scalar : ∀ i : Fin N, ∀ a : Fin 4, JetBound (microScalarFactor a) (scalarCoordinate i z) J C
  pair : ∀ i j : Fin N, JetBound (fun t : ℂ × ℂ × ℂ => regularPairCoefficient t.1 t.2.1 t.2.2)
    (pairCoordinate i j z) J C

 theorem micro_factor_bounds_uniform (s₀ : ℂ) (c : ℝ) (hs : s₀ ≠ 0)
    (hS : s₀+s₀⁻¹=(1+c:ℂ)) (hc : |c|<1) (J : ℕ) :
    ∃ C r : ℝ, 1 ≤ C ∧ 0 < r ∧ ∀ N : ℕ, ∀ s : ℂ, ∀ φ : Fin N → ℂ,
      ‖s-s₀‖ < r → (∀ i, ‖φ i‖ < r) → MicroFactorBounds (s,φ) J C := by
  obtain ⟨Cs,hCs,hsbounds⟩ := micro_scalar_jets_uniform s₀ c hs hS hc J
  obtain ⟨Cp,hCp,hpbounds⟩ := finite_family_jet_bounds
    (fun _ : Fin 1 => fun t : ℂ × ℂ × ℂ => regularPairCoefficient t.1 t.2.1 t.2.2)
    (s₀,0,0) (fun _ => regularPairCoefficient_joint_analytic s₀ c hs hS hc) J
  obtain ⟨rs,hrs,hrsbound⟩ := Metric.eventually_nhds_iff.mp hsbounds
  obtain ⟨rp,hrp,hrpbound⟩ := Metric.eventually_nhds_iff.mp hpbounds
  refine ⟨max Cs Cp,min rs rp,hCs.trans (le_max_left _ _),lt_min hrs hrp,?_⟩
  intro N s φ hs' hφ
  constructor
  · intro i a
    have hd : dist (s,φ i) (s₀,0) < rs := by
      simpa [Prod.dist_eq,dist_eq_norm] using
        And.intro (hs'.trans_le (min_le_left _ _)) ((hφ i).trans_le (min_le_left _ _))
    exact (hrsbound hd a).mono le_rfl (le_max_left _ _)
  · intro i j
    have hd : dist (s,φ i,φ j) (s₀,0,0) < rp := by
      simpa [Prod.dist_eq,dist_eq_norm] using
        And.intro (hs'.trans_le (min_le_right _ _))
          (And.intro ((hφ i).trans_le (min_le_right _ _)) ((hφ j).trans_le (min_le_right _ _)))
    exact (hrpbound hd 0).mono le_rfl (le_max_right _ _)

 theorem microRegularAmplitude_products {N : ℕ} (s : ℂ) (φ : Fin N → ℂ) :
    microRegularAmplitude s φ =
      ((∏ i, Complex.exp (Complex.I*φ i))+(∏ i, (regularY s (φ i))⁻¹))*
      (∏ i, ∏ j ∈ Finset.univ.filter (fun j => i<j), regularPairCoefficient s (φ i) (φ j))*
      ∏ i, microRegularOneBody s (φ i) := by
  have hZ : (regularZProduct s φ)⁻¹=∏ i, Complex.exp (Complex.I*φ i) := by
    rw [regularZProduct,← Complex.exp_neg,show -(-Complex.I*∑ i, φ i)=Complex.I*∑ i, φ i by ring,
      Finset.mul_sum,Complex.exp_sum]
  have hY : (regularYProduct s φ)⁻¹=∏ i, (regularY s (φ i))⁻¹ := by
    simp [regularYProduct]
  rw [microRegularAmplitude,hZ,hY]

 theorem micro_amplitude_jet_product_budget {N : ℕ} (z : ℂ × (Fin N → ℂ))
    (J : ℕ) (C : ℝ) (hC : 1 ≤ C) (h : MicroFactorBounds z J C) :
    JetBound (fun t : ℂ × (Fin N → ℂ) => microRegularAmplitude t.1 t.2) z J
      (2^J*(2^J*((2^J*C)^N+(2^J*C)^N)*(2^J*(2^J*C)^N)^N)*(2^J*C)^N) := by
  have hlift : ∀ i : Fin N, ∀ a : Fin 4,
      JetBound (fun t : ℂ × (Fin N → ℂ) => microScalarFactor a (t.1,t.2 i)) z J C := by
    intro i a
    exact (h.scalar i a).comp (scalarCoordinate i) (scalarCoordinate_norm i)
  have hp : ∀ i j : Fin N, JetBound
      (fun t : ℂ × (Fin N → ℂ) => regularPairCoefficient t.1 (t.2 i) (t.2 j)) z J C := by
    intro i j
    exact (h.pair i j).comp (pairCoordinate i j) (pairCoordinate_norm i j)
  have hscalar (a : Fin 4) : JetBound
      (fun t : ℂ × (Fin N → ℂ) => ∏ i, microScalarFactor a (t.1,t.2 i)) z J ((2^J*C)^N) := by
    simpa using jetBound_finset_product (Finset.univ : Finset (Fin N)) (fun (i : Fin N) (t : ℂ × (Fin N → ℂ)) => microScalarFactor a (t.1,t.2 i))
      z J C (fun i _ => hlift i a)
  have hB : 1 ≤ (2:ℝ)^J*C := by
    have hp : (1:ℝ) ≤ 2^J := one_le_pow₀ (by norm_num)
    nlinarith
  have hpairInner (i : Fin N) : JetBound
      (fun t : ℂ × (Fin N → ℂ) => ∏ j ∈ Finset.univ.filter (fun j => i<j),
        regularPairCoefficient t.1 (t.2 i) (t.2 j)) z J ((2^J*C)^N) := by
    have hh := jetBound_finset_product (Finset.univ.filter (fun j : Fin N => i<j))
      (fun (j : Fin N) (t : ℂ × (Fin N → ℂ)) => regularPairCoefficient t.1 (t.2 i) (t.2 j))
      z J C (fun j _ => hp i j)
    apply hh.mono le_rfl
    exact pow_le_pow_right₀ hB (by simpa using Finset.card_filter_le (s := (Finset.univ : Finset (Fin N))) (p := fun j => i<j))
  have hpair := jetBound_finset_product (Finset.univ : Finset (Fin N))
    (fun (i : Fin N) (t : ℂ × (Fin N → ℂ)) => ∏ j ∈ Finset.univ.filter (fun j => i<j),
      regularPairCoefficient t.1 (t.2 i) (t.2 j)) z J ((2^J*C)^N) (fun i _ => hpairInner i)
  have hh := (((hscalar 2).add (hscalar 1)).mul hpair).mul (hscalar 0)
  convert! hh using 1
  · ext t
    rw [microRegularAmplitude_products]
    simp [microScalarFactor]
  · simp

end
end IsingBulk.Tail
