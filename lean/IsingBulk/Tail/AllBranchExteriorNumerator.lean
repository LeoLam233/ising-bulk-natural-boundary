import IsingBulk.Tail.AllBranchExteriorPairJets
import IsingBulk.Tail.MicrocoreAmplitudeBound
import IsingBulk.Tail.MicrocoreVandermondeBound

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Jets IsingBulk.Branch
open scoped BigOperators

def allBranchExteriorPairProduct {N : ℕ} (z : ℂ × (Fin N → ℂ)) : ℂ :=
  ∏ p ∈ orderedIndexPairs (Finset.univ : Finset (Fin N)), branchCompletePair (z.1,z.2 p.1,z.2 p.2)

theorem allBranchExterior_pair_product_factorization {N : ℕ} (z : ℂ × (Fin N → ℂ)) :
    allBranchExteriorPairProduct z = microcoreVandermondeSquared z.2 *
      (∏ i, ∏ j ∈ Finset.univ.filter (fun j => i<j), regularPairCoefficient z.1 (z.2 i) (z.2 j)) := by
  unfold allBranchExteriorPairProduct orderedIndexPairs branchCompletePair microcoreVandermondeSquared
  simp only [Finset.prod_filter,Finset.prod_product]
  simp_rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  apply Finset.prod_congr rfl
  intro j _
  split_ifs <;> simp

theorem allBranchExterior_unfactored_eq {N : ℕ} (A : ℂ × (Fin N → ℂ) → ℂ)
    (z : ℂ × (Fin N → ℂ)) :
    unfactoredNumerator A z=microcoreVandermondeSquared z.2*A z := by
  unfold unfactoredNumerator microcoreVandermondeSquared
  congr 1
  rw [← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro i _
  rw [← Finset.prod_pow]
  congr 1
  ext j
  simp

theorem allBranchExterior_numerator_factorization {N : ℕ} (z : ℂ × (Fin N → ℂ)) :
    unfactoredNumerator (fun t : ℂ × (Fin N → ℂ) => microRegularAmplitude t.1 t.2) z =
      ((∏ i, microScalarFactor 2 (z.1,z.2 i))+(∏ i, microScalarFactor 1 (z.1,z.2 i)))*
        allBranchExteriorPairProduct z*(∏ i, microScalarFactor 0 (z.1,z.2 i)) := by
  rw [allBranchExterior_unfactored_eq,microRegularAmplitude_products,allBranchExterior_pair_product_factorization]
  simp only [microScalarFactor,show (2:Fin 4) ≠ 0 by decide,show (2:Fin 4) ≠ 1 by decide,
    show (1:Fin 4) ≠ 0 by decide,ite_false,ite_true]
  ring

theorem allBranchExterior_numerator_jet_budget {N : ℕ} (z : ℂ × (Fin N → ℂ))
    (J : ℕ) (C P : ℝ) (hscalar : ∀ i : Fin N, ∀ a : Fin 4,
      JetBound (microScalarFactor a) (scalarCoordinate i z) J C)
    (hpair : JetBound (@allBranchExteriorPairProduct N) z J P) :
    JetBound (unfactoredNumerator (fun t : ℂ × (Fin N → ℂ) => microRegularAmplitude t.1 t.2))
      z J ((2:ℝ)^J*((2:ℝ)^J*((2^J*C)^N+(2^J*C)^N)*P)*(2^J*C)^N) := by
  have hs (a : Fin 4) : JetBound
      (fun t : ℂ × (Fin N → ℂ) => ∏ i, microScalarFactor a (t.1,t.2 i)) z J ((2^J*C)^N) := by
    simpa [Function.comp_def,scalarCoordinate] using jetBound_finset_product Finset.univ _ z J C
      (fun i _ => (hscalar i a).comp (scalarCoordinate i) (scalarCoordinate_norm i))
  have hh := (((hs 2).add (hs 1)).mul hpair).mul (hs 0)
  have he : unfactoredNumerator (fun t : ℂ × (Fin N → ℂ) => microRegularAmplitude t.1 t.2)=
      (fun t => ((∏ i, microScalarFactor 2 (t.1,t.2 i))+(∏ i, microScalarFactor 1 (t.1,t.2 i)))*
        allBranchExteriorPairProduct t*(∏ i, microScalarFactor 0 (t.1,t.2 i))) :=
    funext allBranchExterior_numerator_factorization
  rw [he]
  exact hh

theorem allBranchExterior_pair_uniform_budget (s₀ : ℂ) (c q : ℝ) (hs : s₀ ≠ 0)
    (hS : s₀+s₀⁻¹=(1+c:ℂ)) (hc : |c| < 1) (hq : 0 < q) (hq1 : q ≤ 1) (J : ℕ) :
    ∃ C r : ℝ, 1 ≤ C ∧ 0 < r ∧ ∀ N : ℕ, ∀ z : ℂ × (Fin N → ℂ),
      ‖z.1-s₀‖ < r → (∀ i, ‖z.2 i‖ < r) →
      JetBound (@allBranchExteriorPairProduct N) z J
        (C^J*((N.choose 2:ℝ)+1)^J*q^((N.choose 2:ℤ)-(J:ℤ))) := by
  obtain ⟨C,r,hC,hr,hbound⟩ := allBranchExterior_complete_pair_jets s₀ c q hs hS hc hq hq1 J
  obtain ⟨ra,hra,ha⟩ := Metric.eventually_nhds_iff.mp
    (branchCompletePair_analytic s₀ c hs hS hc).eventually_analyticAt
  refine ⟨C,min r ra,hC,lt_min hr hra,?_⟩
  intro N z hz hφ
  have hrz := hz.trans_le (min_le_left _ _)
  have hrφ := fun i => (hφ i).trans_le (min_le_left _ _)
  have hlocal (p : Fin N × Fin N) : AnalyticAt ℂ branchCompletePair (z.1,z.2 p.1,z.2 p.2) := by
    apply ha
    rw [Prod.dist_eq,Prod.dist_eq,max_lt_iff,max_lt_iff]
    simpa only [dist_eq_norm,sub_zero] using And.intro (hz.trans_le (min_le_right _ _))
      (And.intro ((hφ p.1).trans_le (min_le_right _ _)) ((hφ p.2).trans_le (min_le_right _ _)))
  refine ⟨?_,by positivity,?_⟩
  · apply Finset.analyticAt_fun_prod
    intro p _
    exact AnalyticAt.comp (g := branchCompletePair) (f := pairCoordinate p.1 p.2)
      (hlocal p) ((pairCoordinate p.1 p.2).analyticAt z)
  · intro k hk
    have hh := hbound N z hrz hrφ k hk
    apply hh.trans
    apply mul_le_mul
    · exact mul_le_mul (pow_le_pow_right₀ hC hk)
        ((pow_le_pow_left₀ (Nat.cast_nonneg _) (by linarith : (N.choose 2:ℝ) ≤ (N.choose 2:ℝ)+1) k).trans
          (pow_le_pow_right₀ (by have := Nat.cast_nonneg (N.choose 2) (α := ℝ); linarith) hk))
        (by positivity) (by positivity)
    · exact zpow_le_zpow_right_of_le_one₀ hq hq1 (by omega)
    · positivity
    · positivity

theorem allBranchExterior_numerator_uniform (s₀ : ℂ) (c q : ℝ) (hs : s₀ ≠ 0)
    (hS : s₀+s₀⁻¹=(1+c:ℂ)) (hc : |c| < 1) (hq : 0 < q) (hq1 : q ≤ 1) (J : ℕ) :
    ∃ C r : ℝ, 1 ≤ C ∧ 0 < r ∧ ∀ N : ℕ, ∀ z : ℂ × (Fin N → ℂ),
      ‖z.1-s₀‖ < r → (∀ i, ‖z.2 i‖ < r) →
      JetBound (unfactoredNumerator (fun t : ℂ × (Fin N → ℂ) => microRegularAmplitude t.1 t.2)) z J
        ((2:ℝ)^J*((2:ℝ)^J*((2^J*C)^N+(2^J*C)^N)*
          (C^J*((N.choose 2:ℝ)+1)^J*q^((N.choose 2:ℤ)-(J:ℤ))))*(2^J*C)^N) := by
  obtain ⟨Cs,rs,hCs,hrs,hscalar⟩ := micro_factor_bounds_uniform s₀ c hs hS hc J
  obtain ⟨Cp,rp,hCp,hrp,hpair⟩ := allBranchExterior_pair_uniform_budget s₀ c q hs hS hc hq hq1 J
  refine ⟨max Cs Cp,min rs rp,hCs.trans (le_max_left _ _),lt_min hrs hrp,?_⟩
  intro N z hz hφ
  have hsc := hscalar N z.1 z.2 (hz.trans_le (min_le_left _ _))
    (fun i => (hφ i).trans_le (min_le_left _ _))
  have hpa := hpair N z (hz.trans_le (min_le_right _ _))
    (fun i => (hφ i).trans_le (min_le_right _ _))
  apply allBranchExterior_numerator_jet_budget z J (max Cs Cp)
  · intro i a
    exact (hsc.scalar i a).mono le_rfl (le_max_left _ _)
  · apply hpa.mono le_rfl
    gcongr
    exact le_max_right _ _

end
end IsingBulk.Tail
