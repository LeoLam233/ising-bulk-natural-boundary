import IsingBulk.HT22.Tail.LocalizedActualBoundDensity
import IsingBulk.HT22.Tail.LocalizedMassSupport
import IsingBulk.HT22.Tail.PhysicalSigns
import IsingBulk.HT22.Geometry.SeparatedMass

namespace IsingBulk.HT22.Tail
noncomputable section
open IsingBulk.Preferred22 Geometry Set Filter MeasureTheory
open scoped BigOperators Topology ContDiff ENNReal
set_option backward.isDefEq.respectTransparency false

/-- Fixed-N actual localized original-coefficient derivatives are O(log ε).
The source floor is a genuine zero germ of the original smooth weight;
all descendants and their integrated derivatives are constructed, not assumed. -/
theorem actual_localized_derivative_bound (d : PreferredBranchData) :
    ∃ cap : ℝ,0<cap ∧ cap<d.alpha ∧ ∀ B : PreferredCoareaBump d,B.delta<cap →
    ∃ ε₀ τ₀ δ₀ : ℝ,0<ε₀ ∧0<τ₀ ∧0<δ₀ ∧δ₀<B.delta ∧
    ∀δ : ℝ,δ≤δ₀ → ∀rcut : ℝ→ℝ,PreferredRightCutoffData d B δ rcut →
    ∀n : ℕ,∀W : (Fin (2*n+3)→ℝ)→ℂ,ContDiff ℝ ∞ W →
    ∀ρ : ℝ,0<ρ → (∀x,preferredAngularDiameter x<ρ → W=ᶠ[𝓝 x] fun _=>0) →
    ∀j : ℕ,∃C : ℝ,0<C ∧ ∀negative : Bool,∀ε τ : ℝ,0<ε → ε<ε₀ →0≤τ →τ<τ₀ →
    ‖iteratedDeriv j (localizedObservable negative (2*n+2) d B τ rcut W)
      (IsingBulk.Branch.radialParameter d.alpha ε)‖≤C*(1+|Real.log ε|) := by
  obtain ⟨ci,hci,hcia,hi⟩ := actual_localized_integral_identity d
  obtain ⟨cf,hcf,_,hf⟩ := actual_localized_density_far_bound d
  refine ⟨min ci cf,lt_min hci hcf,lt_of_le_of_lt (min_le_left _ _) hcia,?_⟩
  intro B hB
  obtain ⟨ei,ti,di,hei,hti,hdi,hdiB,hi⟩ := hi B (lt_of_lt_of_le hB (min_le_left _ _))
  obtain ⟨ef,tf,df,hef,htf,hdf,_,hf⟩ := hf B (lt_of_lt_of_le hB (min_le_right _ _))
  obtain ⟨em,tm,dm,hem,htm,hdm,_,hm⟩ := signed_separated_mass d B
  let e := min ei (min ef em)
  let t := min ti (min tf tm)
  let z := min di (min df dm)
  refine ⟨e,t,z,by dsimp [e];positivity,by dsimp [t];positivity,
    by dsimp [z];positivity,lt_of_le_of_lt (by simp [z]) hdiB,?_⟩
  intro δ hδ rcut hcut n W hW ρ hρ hWzero j
  obtain ⟨K,hK,hf⟩ := hf (2*n+3) (by omega) W hW rcut hcut.2.2.1 hcut.2.2.2.1 ρ hρ j
  obtain ⟨C,hC,hm⟩ := hm (2*n) ρ K hρ hK.le
  refine ⟨C,hC,?_⟩
  intro negative ε τ hε hεr hτ hτr
  have hzero : ∀x∈preferredRightAngularBox d B.delta δ (2*n+3),
      preferredAngularDiameter x=0 → W=ᶠ[𝓝 x] fun _=>0 :=
    fun x _ hx => hWzero x (by rw [hx];exact hρ)
  have hi' := hi δ (le_trans hδ (by simp [z])) rcut hcut (n+1)
  rw [show 2*(n+1)=2*n+2 by omega] at hi'
  rw [hi' W hW hzero negative τ hτ (lt_of_lt_of_le hτr (by simp [t])) j ε hε
    (lt_of_lt_of_le hεr (by simp [e]))]
  let P := localizedPhysicalDensity (Physical.constraintSign negative) τ preferredPopulationCutoff B.p B.m rcut W j
    (IsingBulk.Branch.radialParameter d.alpha ε)
  have hpzero (x : Fin (2*n+3)→ℝ) (hx : preferredAngularDiameter x<ρ) : P x=0 :=
    (localizedPhysicalDensity_zero_germ (Physical.constraintSign negative) τ preferredPopulationCutoff B.p B.m rcut W x
      (hWzero x hx) j (IsingBulk.Branch.radialParameter d.alpha ε)).self_of_nhds
  have hpbound (x : Fin (2*n+3)→ℝ) (hx : ∀i,x i∈Icc (-d.b-δ) B.delta) :
      ‖P x‖≤K*signedJacobianResolvent (Physical.constraintAngle negative) d B ε τ x := by
    by_cases hfloor : ρ≤preferredAngularDiameter x
    · have hh := hf (Physical.constraintAngle negative) ε τ hε
        (lt_of_lt_of_le hεr (by simp [e])) hτ (lt_of_lt_of_le hτr (by simp [t])) x
        (fun i => ⟨by have := (hx i).1; have : δ≤df := le_trans hδ (by simp [z]);linarith,
          by have := (hx i).2;linarith⟩) hfloor
      simpa only [P,constraintSign_eq_signed_exp] using hh
    · rw [hpzero x (lt_of_not_ge hfloor),norm_zero]
      unfold signedJacobianResolvent
      positivity
  have hmass := hm (Physical.constraintAngle negative) (Physical.constraintAngle negative) ε τ δ
    (constraintAngle_abs_le_pi negative) hε (lt_of_lt_of_le hεr (by simp [e])) hτ
    (lt_of_lt_of_le hτr (by simp [t])) hcut.1 (le_trans hδ (by simp [z])) (fun x => ‖P x‖)
    hpbound (fun x hx => by rw [hpzero x hx,norm_zero])
  have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmass
  rw [ENNReal.toReal_ofReal (by positivity : 0≤C*(1+|Real.log ε|))] at hh
  unfold signedLiftedIntegral
  apply (norm_integral_le_lintegral_norm _).trans
  rw [localizedNorm_lintegral_eq_signedRightRegion (Physical.constraintSign negative)
    (Physical.constraintAngle negative) d B τ rcut W hcut j]
  exact hh

end
end IsingBulk.HT22.Tail
