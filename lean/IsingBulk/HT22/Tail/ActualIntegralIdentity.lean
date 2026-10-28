import IsingBulk.HT22.Tail.SignedRadialIntegralMass
import IsingBulk.HT22.Tail.PhysicalSigns
import IsingBulk.HT22.SmallTube.Mass
import IsingBulk.HT22.Far.WholeMass
import IsingBulk.HT22.Transport.FieldNeighborhood.ActualAngularFrameJets

/-! Unconditional original signed right-coefficient derivative identity. Every
mass, source-domain and flux estimate is supplied by the new actual transport. -/
namespace IsingBulk.HT22.Tail
noncomputable section
open IsingBulk.Preferred22 Set MeasureTheory
open scoped BigOperators Topology ContDiff ENNReal
set_option backward.isDefEq.respectTransparency false

theorem actual_right_integral_identity (d : PreferredBranchData) :
    ∃ cap : ℝ, 0<cap ∧ cap<d.alpha ∧ ∀ B : PreferredCoareaBump d, B.delta<cap →
    ∃ ε₀ τ₀ δ₀ : ℝ, 0<ε₀ ∧ 0<τ₀ ∧ 0<δ₀ ∧ δ₀<B.delta ∧
    ∀ δ : ℝ, δ≤δ₀ → ∀ rcut : ℝ → ℝ, PreferredRightCutoffData d B δ rcut →
    ∀ k n : ℕ, 2*k+9≤(2*n+3)^2 → ∀ negative : Bool, ∀ τ : ℝ, 0≤τ → τ<τ₀ →
    ∀ j : ℕ, j≤k → ∀ ε : ℝ, 0<ε → ε<ε₀ →
      iteratedDeriv j (Physical.rightPopulationIntegral negative (2*n+2) τ
        preferredPopulationCutoff B.p B.m rcut) (IsingBulk.Branch.radialParameter d.alpha ε)=
      transportedIntegral negative (2*n+2) B.delta τ preferredPopulationCutoff B.p B.m rcut j
        (IsingBulk.Branch.radialParameter d.alpha ε) := by
  obtain ⟨cr,hcr,hcra,hr⟩ := actual_regularPoint d
  obtain ⟨cf,hcf,_,hf⟩ := actual_angular_field_diameter_bound_from_jets d
  obtain ⟨cw,hcw,_,hw⟩ := Far.actual_whole_angular_mass d
  obtain ⟨cs,hcs,_,hs⟩ := SmallTube.actual_small_tube_mass d
  refine ⟨min cr (min cf (min cw cs)),by positivity,lt_of_le_of_lt (min_le_left _ _) hcra,?_⟩
  intro B hB
  obtain ⟨er,tr,dr,her,htr,hdr,_,hr⟩ := hr B (lt_of_lt_of_le hB (by simp))
  obtain ⟨C,ef,tf,df,hC,hef,htf,hdf,_,hf⟩ := hf B (lt_of_lt_of_le hB (by simp))
  obtain ⟨ew,tw,dw,hew,htw,hdw,_,hw⟩ := hw B (lt_of_lt_of_le hB (by simp))
  obtain ⟨es,ts,ds,hes,hts,hds,hdsB,hs⟩ := hs B (lt_of_lt_of_le hB (by simp))
  let e := min er (min ef (min ew es))
  let t := min tr (min tf (min tw ts))
  let z := min dr (min df (min dw ds))
  have ez : 0<e := by dsimp [e]; positivity
  have tz : 0<t := by dsimp [t]; positivity
  have zz : 0<z := by dsimp [z]; positivity
  refine ⟨e,t,z,ez,tz,zz,lt_of_le_of_lt (by simp [z]) hdsB,?_⟩
  intro δ hδ rcut hcut k n hdeg negative τ hτ hτt
  have hreg : ∀ ε : ℝ,0<ε → ε<e → ∀ x∈preferredRightAngularBox d B.delta δ (2*(n+1)+1),
      0<preferredAngularDiameter x → RegularPoint τ B.p B.m (IsingBulk.Branch.radialParameter d.alpha ε) x := by
    intro ε hε hεe x hx hxD
    apply hr _ (by omega) ε τ hε (lt_of_lt_of_le hεe (by simp [e])) hτ
      (lt_of_lt_of_le hτt (by simp [t])) x _ hxD
    intro i
    exact ⟨by have := (hx i).1; have : δ≤dr := le_trans hδ (by simp [z]); linarith,
      (hx i).2⟩
  have hm : ∀ j : ℕ,j≤k → ∀ ε : ℝ,0<ε → ε<e →
      (∫⁻ x : Fin (2*(n+1)) → ℝ in angularBox (2*(n+1)), ENNReal.ofReal
        ‖transportedDensity (Physical.constraintSign negative) τ preferredPopulationCutoff B.p B.m rcut j
          (IsingBulk.Branch.radialParameter d.alpha ε)
          (preferredLiftedAngles B.delta (constrainedAtTotal (Physical.constraintAngle negative) x))‖)<(⊤:ℝ≥0∞) := by
    intro j hj ε hε hεe
    obtain ⟨H,A,L,_,_,hb⟩ := hw rcut hcut.2.2.1 hcut.2.2.2.1 j
    have hb := hb (Physical.constraintAngle negative) (Physical.constraintAngle negative)
      (constraintAngle_abs_le_pi negative) n (by omega) ε τ hε
      (lt_of_lt_of_le hεe (by simp [e])) hτ (lt_of_lt_of_le hτt (by simp [t])) δ
      (le_trans hδ (by simp [z])) hcut
    have hh := lt_of_le_of_lt hb ENNReal.ofReal_lt_top
    rw [show 2*(n+1)=2*n+2 by omega]
    simpa only [constraintSign_eq_signed_exp] using hh
  have hmS : ∀ j : ℕ,j≤k → ∃ F : ℝ,0<F ∧ ∀ ε : ℝ,0<ε → ε<e → ∀ m : ℕ,
      (∫⁻ x : Fin (2*(n+1)) → ℝ in angularBox (2*(n+1)),
        smallMassIntegrand (Physical.constraintAngle negative) (Physical.constraintSign negative)
          d B τ rcut j (IsingBulk.Branch.radialParameter d.alpha ε) (preferredDyadicRadius m) x)≤
        ENNReal.ofReal (F*(1+|Real.log ε|)*(1/8:ℝ)^m) := by
    intro j hj
    obtain ⟨F,hF,hFs⟩ := hs δ (le_trans hδ (by simp [z])) rcut hcut j n (by omega)
    refine ⟨F,hF,?_⟩
    intro ε hε hεe m
    have hb := hFs (Physical.constraintAngle negative) (Physical.constraintAngle negative) ε τ
      (constraintAngle_abs_le_pi negative) hε (lt_of_lt_of_le hεe (by simp [e])) hτ
      (lt_of_lt_of_le hτt (by simp [t])) m
    rw [show 2*(n+1)=2*n+2 by omega]
    simpa only [constraintSign_eq_signed_exp] using hb
  have hfield : ∀ ε : ℝ,0<ε → ε<e → ∀ θ : Fin (2*(n+1)+1) → ℝ,
      θ∈preferredRightAngularBox d B.delta δ (2*(n+1)+1) → 0<preferredAngularDiameter θ →
      ∀ i,‖angularField τ B.p B.m (IsingBulk.Branch.radialParameter d.alpha ε) θ i‖≤
        (C*((2*(n+1)+1:ℕ):ℝ))*((2*(n+1)+1:ℕ):ℝ)^2/preferredAngularDiameter θ := by
    intro ε hε hεe θ hθ hD i
    have hbox : ∀ a,-df≤θ a+d.b ∧ θ a+d.b≤d.b+B.delta := by
      intro a
      exact ⟨by have := (hθ a).1; have : δ≤df := le_trans hδ (by simp [z]); linarith,
        by linarith [(hθ a).2]⟩
    have hh := hf _ (by omega) ε τ hε (lt_of_lt_of_le hεe (by simp [e])) hτ
      (lt_of_lt_of_le hτt (by simp [t])) θ hbox hD i
    convert hh using 1; ring

  have hi := right_integral_identity_of_smallMass negative (n+1) (by omega) d B hτ rcut hcut k
    hreg hm hmS (mul_pos hC (by positivity)) hfield
  simpa only [Nat.mul_add,Nat.mul_one] using hi

end
end IsingBulk.HT22.Tail
