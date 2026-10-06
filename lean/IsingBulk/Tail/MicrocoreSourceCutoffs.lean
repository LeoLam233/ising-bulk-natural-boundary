import IsingBulk.Tail.MicrocoreTheorem
import IsingBulk.Tail.PeriodicBranchCutoffs

/-! The localized microcore is the literal original all-B selector piece:
its support lies where both the angular selector and every branch cutoff are one. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Branch IsingBulk.First IsingBulk.Jets IsingBulk.PrimeFamily MeasureTheory Filter
open scoped BigOperators Topology

def allBranchWeight {N : ℕ} (b δ : ℝ) (hδ : 0 < δ) (θ : Fin N → ℝ) : ℝ :=
  ∏ i, periodicBranchChi b δ hδ (θ i)

theorem microcore_selector_branch_plateau {N : ℕ} (b δ α η r : ℝ)
    (hb : 0 < b) (hbπ : b < Real.pi) (hδ : 0 < δ) (hδs : δ ≤ 1/2) (hα : 0 < α)
    (hrδ : r ≤ δ/2) (hrb : r ≤ b/2) (hrπ : r ≤ (Real.pi-b)/2)
    (u : Fin N → ℝ) (hu : ∀ i, |u i| ≤ r) :
    angularSelector (constructedSelector b η α) (fun i => u i-b)=1 ∧
      allBranchWeight b δ hδ (fun i => u i-b)=1 := by
  have hbump : ∀ i, periodicBranchChi b δ hδ (u i-b)=1 := by
    intro i
    have hui := abs_le.mp (hu i)
    have hπ : 1 < Real.pi := by linarith [Real.pi_gt_three]
    rw [show u i-b=-b+u i by ring,periodicBranchChi_local b δ (u i) hδ (by linarith) (by linarith)]
    exact fixedBranchBump_one δ hδ ((hu i).trans hrδ)
  have ha : ∀ i, (constructedSelector b η α).a (u i-b)=0 := by
    intro i
    have hui := abs_le.mp (hu i)
    have hangle : -Real.pi < u i-b ∧ u i-b < 0 := by constructor <;> linarith
    have hsin := Real.sin_neg_of_neg_of_neg_pi_lt hangle.2 hangle.1
    exact thresholdStep_zero (by linarith) (by linarith)
  constructor
  · simp [angularSelector,selectorWeight,ha]
  · simp [allBranchWeight,hbump]

theorem microcore_all_branch_weight_identity {N : ℕ} (b δ α η r : ℝ)
    (hb : 0 < b) (hbπ : b < Real.pi) (hδ : 0 < δ) (hδs : δ ≤ 1/2) (hα : 0 < α)
    (hr : 0 < r) (hrδ : r ≤ δ/2) (hrb : r ≤ b/2) (hrπ : r ≤ (Real.pi-b)/2)
    (u : Fin N → ℝ) :
    scaledMicroCutoff N r u*angularSelector (constructedSelector b η α) (fun i => u i-b)*
      allBranchWeight b δ hδ (fun i => u i-b)=scaledMicroCutoff N r u := by
  by_cases hw : scaledMicroCutoff N r u=0
  · simp [hw]
  · have hu := scaledMicroCutoff_jet_tsupport hr [] (subset_closure hw)
    obtain ⟨ha,hB⟩ := microcore_selector_branch_plateau b δ α η r hb hbπ hδ hδs hα hrδ hrb hrπ u hu
    rw [ha,hB,mul_one,mul_one]

def allBranchMicrocoreIntegral (n : ℕ) (d : LocalBranchData) (η δ : ℝ) (hδ : 0 < δ)
    (ε r : ℝ) (s : ℂ) : ℂ :=
  ((n+2).factorial:ℂ)⁻¹*∫ u : Fin (n+2) → ℝ,
    (scaledMicroCutoff (n+2) r u*angularSelector (constructedSelector d.thetaB η d.alpha)
      (fun i => u i-d.thetaB)*allBranchWeight d.thetaB δ hδ (fun i => u i-d.thetaB):ℝ)*
      sourceReducedAngularDensity (Real.exp (-d.c₀*ε)) s (fun i => u i-d.thetaB)

theorem allBranchMicrocoreIntegral_eq (n : ℕ) (d : LocalBranchData) (η δ ε r : ℝ)
    (hδ : 0 < δ) (hδs : δ ≤ 1/2) (hr : 0 < r)
    (hrδ : r ≤ δ/2) (hrb : r ≤ d.thetaB/2) (hrπ : r ≤ (Real.pi-d.thetaB)/2) :
    allBranchMicrocoreIntegral n d η δ hδ ε r=originalMicrocoreIntegral n d ε r := by
  funext s
  unfold allBranchMicrocoreIntegral originalMicrocoreIntegral
  simp_rw [microcore_all_branch_weight_identity d.thetaB δ d.alpha η r d.thetaB_pos d.thetaB_lt
    hδ hδs d.alpha_pos hr hrδ hrb hrπ]

/-- Exact original all-B microcore contribution for the immutable selected
family. Both source partition factors are retained in the integral. -/
theorem selected_all_branch_microcore {p : ℕ} (hp : p.Prime) {a b : ℤ}
    (ha : Admissible p a) (hb : Admissible p b) (τ α : ℝ) (hτ : 0 < τ) (hα : 0 < α)
    (η δ : ℝ) (hδ : 0 < δ) (hδs : δ ≤ 1/2) (J : ℕ) (D : ℝ) (hD : 0 ≤ D) :
    let d := selectedLocalBranchData ha hb τ α hτ hα
    ∃ A c E : ℝ, 0 < A ∧ 0 < c ∧ c ≤ 1/4 ∧ c ≤ δ/2 ∧ 0 < E ∧
      Summable (microcoreMajorant A c E) ∧
      ∀ᶠ H : ℝ in atTop, ∀ n : ℕ, ((n+2:ℕ):ℝ) ≤ D*Real.sqrt H →
        let ε := Real.exp (-H)
        let bN := microcoreRadius A c (n+2)
        ∀ j ≤ J,
          ‖iteratedDeriv j (allBranchMicrocoreIntegral n d η δ hδ ε bN) (radialParameter d.theta ε)‖ ≤
            Real.exp (E*((n+2:ℕ):ℝ)^2)*bN^((((n+2:ℕ):ℝ)^2-1)/2) := by
  let d := selectedLocalBranchData ha hb τ α hτ hα
  let cap := min (δ/2) (min (d.thetaB/2) ((Real.pi-d.thetaB)/2))
  have hcap : 0 < cap := by
    have h1 := d.thetaB_pos
    have h2 : 0 < Real.pi-d.thetaB := sub_pos.mpr d.thetaB_lt
    dsimp [cap]
    positivity
  obtain ⟨A,c,E,hA,hc,hcs,hcCap,hE,hSum,hbound⟩ :=
    selected_nonresonant_microcore hp ha hb τ α hτ hα cap hcap J D hD
  refine ⟨A,c,E,hA,hc,hcs,hcCap.trans (min_le_left _ _),hE,hSum,?_⟩
  filter_upwards [hbound] with H hH
  intro n hwindow
  dsimp only
  intro j hj
  have hbN := microcoreRadius_pos A c hc (n+2) (by omega)
  have hbc := microcoreRadius_le_prefactor A c hA.le hc.le (n+2) (by omega)
  have hδN := hbc.trans (hcCap.trans (min_le_left _ _))
  have hbN' := hbc.trans (hcCap.trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hπN := hbc.trans (hcCap.trans ((min_le_right _ _).trans (min_le_right _ _)))
  rw [allBranchMicrocoreIntegral_eq n d η δ _ _ hδ hδs hbN hδN hbN' hπN]
  exact hH n hwindow j hj

end
end IsingBulk.Tail
