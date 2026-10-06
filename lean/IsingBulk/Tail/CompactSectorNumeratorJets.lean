import IsingBulk.Tail.SectorJointRealJets
import IsingBulk.Tail.ActualCompactGaussianJets

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Set Filter
open scoped Topology ContDiff BigOperators
set_option maxHeartbeats 1800000

theorem original_sector_selector_support {N : ℕ} (f : SelectorFunctions)
    (b outer inner : ℝ) (ho : 0 < outer) (hi : 0 < inner) (q : Fin N) (sigma : Fin N → Fin 3) :
    tsupport (originalSectorAngularWeight f b outer inner ho hi q sigma) ⊆ tsupport (angularSelector f) :=
  tsupport_mul_subset_left.trans (tsupport_comp_subset (g := Complex.ofReal) (by simp) _)

theorem current_sector_selector_support {N : ℕ} (f : SelectorFunctions)
    (τ b outer inner : ℝ) (ho : 0 < outer) (hi : 0 < inner) (qS q : Fin N) (sigma : Fin N → Fin 3) :
    tsupport (currentSectorAngularWeight f τ qS b outer inner ho hi q sigma) ⊆
      tsupport (namedSelectorDerivative f qS) :=
  tsupport_mul_subset_left.trans (tsupport_mul_subset_right.trans
    (tsupport_comp_subset (g := Complex.ofReal) (by simp) _))

theorem angular_weighted_zero_jets {N J : ℕ} (w : (Fin N → ℝ) → ℂ)
    (A : ℂ × (Fin N → ℝ) → ℂ) {p : ℂ × (Fin N → ℝ)}
    (hp : p.2 ∉ tsupport w) {ρ C : ℝ} (hρ : 0 ≤ ρ) (hC : 0 ≤ C) (a : ℤ) :
    RealScaledJetBound (fun q => w q.2*A q) p J ρ C a := by
  apply (RealScaledJetBound.zero p J ρ C a hρ hC).congr
  have hz := (notMem_tsupport_iff_eventuallyEq.mp hp).comp_tendsto continuous_snd.continuousAt.tendsto
  filter_upwards [hz] with q hq
  rw [show w q.2=0 from hq,zero_mul]

theorem compact_sector_gaussian_product {N J : ℕ} (hN : 0 < N)
    (w : (Fin N → ℝ) → ℂ) (A : ℂ × (Fin N → ℝ) → ℂ) (p : ℂ × (Fin N → ℝ))
    {B C κ : ℝ} (hB : 1 ≤ B) (hC : 1 ≤ C)
    (hw : RealScaledJetBound (fun q : ℂ × (Fin N → ℝ) => w q.2) p J 1 (B^N*(N:ℝ)^J) 0)
    (hA : p.2 ∈ tsupport w → RealScaledJetBound A p J 1
      (C^N*(N:ℝ)^(5*J)*Real.exp (-κ*(N:ℝ)^2)) 0) :
    RealScaledJetBound (fun q => w q.2*A q) p J 1
      ((2^J*B*C)^N*(N:ℝ)^(6*J)*Real.exp (-κ*(N:ℝ)^2)) 0 := by
  by_cases hs : p.2 ∈ tsupport w
  · have hh := hw.mul (hA hs) zero_lt_one
    simp only [zero_add] at hh
    apply hh.mono zero_lt_one le_rfl
    have h2 : (2:ℝ)^J ≤ (2^J)^N := le_self_pow₀ (one_le_pow₀ (by norm_num)) (by omega)
    have hcost : 2^J*(B*C)^N ≤ (2^J*B*C)^N := by
      calc
        _ ≤ (2^J)^N*(B*C)^N := mul_le_mul_of_nonneg_right h2 (by positivity)
        _ = _ := by rw [← mul_pow]; congr 1; ring
    calc
      _ = 2^J*(B*C)^N*(N:ℝ)^(6*J)*Real.exp (-κ*(N:ℝ)^2) := by
        rw [show 6*J=J+5*J by omega,pow_add,mul_pow]
        ring
      _ ≤ _ := by gcongr
  · exact angular_weighted_zero_jets w A hs zero_le_one (by positivity) 0

theorem compact_sector_collision_product {N J : ℕ}
    (w : (Fin N → ℝ) → ℂ) (A : ℂ × (Fin N → ℝ) → ℂ) (p : ℂ × (Fin N → ℝ))
    {ρ B C : ℝ} {a : ℤ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hB : 1 ≤ B) (hC : 1 ≤ C)
    (hw : RealScaledJetBound (fun q : ℂ × (Fin N → ℝ) => w q.2) p J 1 (B^N*(N:ℝ)^J) 0)
    (hA : RealScaledJetBound A p J ρ (compactNearNumeratorCost C N J) a) :
    RealScaledJetBound (fun q => w q.2*A q) p J ρ
      (2^(3*J)*(B+C)^(2*N^2+2*N)*(N:ℝ)^(8*J)) a := by
  have hh := (hw.rescale_zero hρ hρ1).mul hA hρ
  simp only [zero_add] at hh
  apply hh.mono hρ le_rfl
  have hBC : B^N*C^(2*N^2+N) ≤ (B+C)^(2*N^2+2*N) := by
    calc
      _ ≤ (B+C)^N*(B+C)^(2*N^2+N) := by gcongr <;> linarith
      _ = _ := by rw [← pow_add]; congr 1; omega
  calc
    _ = 2^(3*J)*(B^N*C^(2*N^2+N))*(N:ℝ)^(8*J) := by
      unfold compactNearNumeratorCost
      rw [show 3*J=J+2*J by omega,show 8*J=J+7*J by omega]
      simp only [pow_add]
      ring
    _ ≤ _ := by gcongr

theorem actual_compact_sector_collision_jets (d : LocalBranchData)
    (f : SelectorFunctions) (hf : RegularSelector f) (hp1 : ∀ x, f.p x ≤ 1) {a b : ℝ}
    (hmargin : ∀ θ ∈ Icc a b, |1+Real.cos d.thetaB-Real.cos θ| < 1)
    (outer inner : ℝ) (ho : 0 < outer) (hi : 0 < inner) (J : ℕ) :
    ∃ δ C : ℝ, 0 < δ ∧ 1 ≤ C ∧
      ∀ N : ℕ, 0 < N → ∀ eps τ lam : ℝ, 0 < eps → 0 ≤ τ → τ ≤ 1 →
      0 ≤ lam → lam ≤ 1 → ∀ s : ℂ, s ∈ dampingDomain (Real.exp (-d.c₀*eps)) →
      ‖s-radialParameter d.theta 0‖+d.c₀*eps+2*lam ≤ δ →
      ∀ θ : Fin N → ℝ, (∀ i, θ i ∈ Icc a b) → ∀ q : Fin N, ∀ sigma : Fin N → Fin 3,
      ∀ P : Finset (Fin N × Fin N), P ⊆ orderedIndexPairs Finset.univ →
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 → (∀ ij ∈ P, |θ ij.1-θ ij.2| ≤ ρ) →
      let A := fun z : ℂ × (Fin N → ℝ) => compactRegularDensity f (Real.exp (-d.c₀*eps)) τ lam z.1 z.2
      let B := 2^(3*J)*C^(2*N^2+2*N)*(N:ℝ)^(8*J)
      RealScaledJetBound (fun z : ℂ × (Fin N → ℝ) =>
        originalSectorAngularWeight f d.thetaB outer inner ho hi q sigma z.2*A z)
        (s,θ) J ρ B (2*(P.card:ℤ)) ∧
      ∀ qS : Fin N, RealScaledJetBound (fun z : ℂ × (Fin N → ℝ) =>
        currentSectorAngularWeight f τ qS d.thetaB outer inner ho hi q sigma z.2*A z)
        (s,θ) J ρ B (2*(P.card:ℤ)) := by
  obtain ⟨δ,C,hδ,hC,hA⟩ := actual_compact_regular_numerator_collision_jets d f hf hp1 hmargin J
  obtain ⟨B,hB,hw⟩ := sector_joint_real_jets_common f hf d.thetaB outer inner ho hi J
  refine ⟨δ,B+C,hδ,by linarith,?_⟩
  intro N hN eps τ lam heps hτ hτ1 hlam hlam1 s hs hsmall θ hθ q sigma P hP ρ hρ hρ1 hgap
  have ha := hA N hN eps τ lam heps hτ hτ1 hlam hlam1 s hs hsmall θ hθ P hP ρ hρ hρ1 hgap
  exact ⟨compact_sector_collision_product _ _ _ hρ hρ1 hB hC (hw N hN q sigma (s,θ)).1 ha,
    fun qS => compact_sector_collision_product _ _ _ hρ hρ1 hB hC
      ((hw N hN q sigma (s,θ)).2 τ hτ hτ1 qS) ha⟩

end
end IsingBulk.Tail
