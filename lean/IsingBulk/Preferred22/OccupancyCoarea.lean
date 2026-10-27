import IsingBulk.Preferred22.BumpCoarea

/-!
# Preferred22: restoring the actual occupancy dependence

This module uses the actual normalized occupancies from `deformedAngles`.
It never moves them along an auxiliary transposition path.
-/
namespace IsingBulk.Preferred22
noncomputable section
open scoped BigOperators Topology
open Set Filter

def actualBumpSlopeVector {N : ℕ} (d : PreferredBranchData) (B : PreferredCoareaBump d)
    (ε τ : ℝ) (θ : Fin N → ℝ) (i : Fin N) : ℂ :=
  preferredCompactSlope d B.m B.p ε τ (occupancy B.p θ/(N:ℝ))
    (occupancy B.m θ/(N:ℝ)) (θ i)

/-- Both complete occupancy corrections in the actual extreme direction. -/
def actualOccupancyCorrection {N : ℕ} (d : PreferredBranchData) (B : PreferredCoareaBump d)
    (ε τ : ℝ) (θ : Fin N → ℝ) (i j : Fin N) : ℂ :=
  -(Complex.I*(τ:ℂ)/(N:ℂ))*(((deriv B.p (θ i):ℝ):ℂ)-((deriv B.p (θ j):ℝ):ℂ))*
    (∑ v, (B.m (θ v):ℂ)*actualBumpSlopeVector d B ε τ θ v)+
  (Complex.I*(τ:ℂ)/(N:ℂ))*(((deriv B.m (θ i):ℝ):ℂ)-((deriv B.m (θ j):ℝ):ℂ))*
    (∑ v, (B.p (θ v):ℂ)*actualBumpSlopeVector d B ε τ θ v)

/-- G5 restored to the literal original constrained integral: its real
extreme-path derivative is the fixed-occupancy comparison gap plus the two
actual global occupancy corrections, with no omissions. -/
theorem actual_extreme_phase_derivative {N : ℕ} (hN : 0 < N)
    (d : PreferredBranchData) (B : PreferredCoareaBump d)
    {ε τ : ℝ} (hε : 0 < ε) (hτ : 0 ≤ τ) (θ : Fin N → ℝ) (i j : Fin N) :
    deriv (fun h : ℝ => preferredTotalPhase d ε τ B.p B.m (extremeAnglePath θ i j h)) 0 =
      (fixedOccupancySlope d B ε τ (occupancy B.p θ/(N:ℝ))
          (occupancy B.m θ/(N:ℝ)) (θ i+d.b)-
        fixedOccupancySlope d B ε τ (occupancy B.p θ/(N:ℝ))
          (occupancy B.m θ/(N:ℝ)) (θ j+d.b))+
        actualOccupancyCorrection d B ε τ θ i j := by
  have hp (v : Fin N) : HasDerivAt B.p (deriv B.p (θ v)) (θ v) :=
    ((contDiff_infty_iff_deriv.mp B.smooth).1 (θ v)).hasDerivAt
  have hm (v : Fin N) : HasDerivAt B.m (deriv B.m (θ v)) (θ v) :=
    ((contDiff_infty_iff_deriv.mp B.m_smooth).1 (θ v)).hasDerivAt
  have hφ (v : Fin N) : HasDerivAt (preferredAngularPhase d ε)
      (actualBumpSlopeVector d B ε τ θ v) (deformedAngles τ B.p B.m θ v) :=
    actual_bump_phase_hasDerivAt hN d B hε hτ θ v
  have h := (hasDerivAt_totalPhase_extreme τ i j hp hm hφ).deriv
  rw [occupancy_extreme_difference] at h
  have hb (v : Fin N) :
      actualBumpSlopeVector d B ε τ θ v *
        (1-(Complex.I*((τ/(N:ℝ):ℝ):ℂ))*
          ((∑ z, (B.p (θ z):ℂ))*((deriv B.m (θ v):ℝ):ℂ)-
            (∑ z, (B.m (θ z):ℂ))*((deriv B.p (θ v):ℝ):ℂ))) =
      fixedOccupancySlope d B ε τ (occupancy B.p θ/(N:ℝ))
        (occupancy B.m θ/(N:ℝ)) (θ v+d.b) := by
    unfold fixedOccupancySlope actualBumpSlopeVector
    rw [show -d.b+(θ v+d.b) = θ v by ring]
    unfold preferredBumpTangent occupancy
    push_cast
    ring
  rw [hb i,hb j] at h
  have hκ : Complex.I*((τ/(N:ℝ):ℝ):ℂ) = Complex.I*(τ:ℂ)/(N:ℂ) := by push_cast; ring
  rw [hκ] at h
  change deriv (fun h : ℝ => preferredTotalPhase d ε τ B.p B.m (extremeAnglePath θ i j h)) 0 = _ at h
  rw [h]
  unfold actualOccupancyCorrection
  ring


/-- The regular-coordinate Jacobian factor 1+b has the same one-body
square-root envelope on a bounded right interval. -/
theorem shifted_slope_bound {z : ℂ} {A L R : ℝ}
    (hL : 0 < L) (hLR : L ≤ R) (hz : ‖z‖ ≤ A/Real.sqrt L) :
    ‖z+1‖ ≤ (A+Real.sqrt R)/Real.sqrt L := by
  have hs := Real.sqrt_pos.mpr hL
  calc
    ‖z+1‖ ≤ ‖z‖+1 := by simpa only [norm_one] using norm_add_le z (1:ℂ)
    _ ≤ A/Real.sqrt L+1 := by linarith
    _ = (A+Real.sqrt L)/Real.sqrt L := by field_simp
    _ ≤ _ := div_le_div_of_nonneg_right (by linarith [Real.sqrt_le_sqrt hLR]) hs.le

/-- The correction norm for actual source bumps, with their derivative
Lipschitz constants derived from smoothness rather than supplied as data. -/
theorem actual_source_occupancy_error_bound (d : PreferredBranchData) (B : PreferredCoareaBump d) :
    ∃ K : ℝ, 0 < K ∧ ∀ N : ℕ, 0 < N → ∀ ε τ : ℝ, 0 ≤ τ →
      ∀ θ : Fin N → ℝ, ∀ i j : Fin N,
      θ i ∈ Icc (-d.b) B.delta → θ j ∈ Icc (-d.b) B.delta → θ i ≤ θ j →
      ∀ A : ℝ, 0 ≤ A → (∀ v, ‖actualBumpSlopeVector d B ε τ θ v‖ ≤ A) →
      ‖actualOccupancyCorrection d B ε τ θ i j‖ ≤ 2*τ*K*(θ j-θ i)*A := by
  obtain ⟨K,hK,hdiff⟩ := B.derivative_differences
  refine ⟨K,hK,?_⟩
  intro N hN ε τ hτ θ i j hi hj hij A hA hb
  obtain ⟨hdp,hdm⟩ := hdiff (θ i) (θ j) hi hj hij
  have hpv (v : Fin N) : ‖(B.p (θ v):ℂ)‖ ≤ 1 := by
    simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (B.lower_bound (θ v))] using B.upper_bound (θ v)
  have hmv (v : Fin N) : ‖(B.m (θ v):ℂ)‖ ≤ 1 := by
    simpa only [PreferredCoareaBump.m,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (B.lower_bound (-θ v))] using B.upper_bound (-θ v)
  have hdp' : ‖((deriv B.p (θ i):ℝ):ℂ)-((deriv B.p (θ j):ℝ):ℂ)‖ ≤ K*(θ j-θ i) := by
    simpa only [← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] using hdp
  have hdm' : ‖((deriv B.m (θ i):ℝ):ℂ)-((deriv B.m (θ j):ℝ):ℂ)‖ ≤ K*(θ j-θ i) := by
    simpa only [← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] using hdm
  exact actual_occupancy_correction_norm hN hτ hK.le (sub_nonneg.mpr hij) hA
    hpv hmv hb hdp' hdm'


def actualExtremeProjection {N : ℕ} (d : PreferredBranchData) (B : PreferredCoareaBump d)
    (ε τ : ℝ) (θ : Fin N → ℝ) (i j : Fin N) : ℝ :=
  (preferredCompactDirection*deriv (fun h : ℝ =>
    preferredTotalPhase d ε τ B.p B.m (extremeAnglePath θ i j h)) 0).re

theorem preferredCompactDirection_norm : ‖preferredCompactDirection‖ = 1 := by
  unfold preferredCompactDirection
  rw [Complex.norm_exp]
  simp only [Complex.mul_re,Complex.neg_re,Complex.I_re,Complex.ofReal_im]
  norm_num

set_option maxHeartbeats 1000000 in
/-- The complete actual-occupancy extreme estimate. All comparison constants
are derived before N and the actual configuration; both occupancy corrections
are restored and absorbed only at that configuration. -/
theorem preferred_actual_extreme_estimate (d : PreferredBranchData) (B : PreferredCoareaBump d) :
    ∃ C ε0 τ0 : ℝ, 0 < C ∧ 0 < ε0 ∧ 0 < τ0 ∧
      ∀ N : ℕ, 0 < N → ∀ ε τ : ℝ, 0 < ε → ε < ε0 → 0 ≤ τ → τ < τ0 →
      ∀ θ : Fin N → ℝ, (∀ v, θ v ∈ Icc (-d.b) B.delta) → ∀ i j : Fin N,
      (∀ v, θ i ≤ θ v) → (∀ v, θ v ≤ θ j) → θ i < θ j →
      0 < actualExtremeProjection d B ε τ θ i j ∧
      ‖(actualBumpSlopeVector d B ε τ θ i+1)*(actualBumpSlopeVector d B ε τ θ j+1)‖/
          actualExtremeProjection d B ε τ θ i j ≤
        C*Real.sqrt (θ j+d.b+ε)/(θ j-θ i) := by
  obtain ⟨k,εg,τg,hk,hεg,hτg,hgap⟩ := preferred_fixed_occupancy_extreme_gap d B
  obtain ⟨_,A,εs,τs,_,hA,hεs,hτs,hsource⟩ := preferred_full_right_projection d B
  obtain ⟨K,hK,herror⟩ := actual_source_occupancy_error_bound d B
  let R := d.b+B.delta+2
  have hR : 0 < R := by dsimp [R]; have := d.b_pos; have := B.delta_pos; positivity
  let A' := A+Real.sqrt R
  have hA' : 0 < A' := by dsimp [A']; positivity
  let Ce := 2+1/d.b
  have hCe : 0 < Ce := by dsimp [Ce]; have := d.b_pos; positivity
  let C := (A'^2/(k/2))*Real.sqrt Ce
  have hC : 0 < C := by dsimp [C]; positivity
  let ε0 := min 1 (min εg εs)
  have hε0 : 0 < ε0 := lt_min (by norm_num) (lt_min hεg hεs)
  let τ0 := min 1 (min τg (min τs (k/(4*K*A*R))))
  have hτ0 : 0 < τ0 := by dsimp [τ0]; positivity
  have hε01 : ε0 ≤ 1 := min_le_left _ _
  have hε0g : ε0 ≤ εg := (min_le_right _ _).trans (min_le_left _ _)
  have hε0s : ε0 ≤ εs := (min_le_right _ _).trans (min_le_right _ _)
  have hτ01 : τ0 ≤ 1 := min_le_left _ _
  have hτ0g : τ0 ≤ τg := (min_le_right _ _).trans (min_le_left _ _)
  have hτ0s : τ0 ≤ τs := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hτ0abs : τ0 ≤ k/(4*K*A*R) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨C,ε0,τ0,hC,hε0,hτ0,?_⟩
  intro N hN ε τ hε hεr hτ hτr θ hθ i j hmin hmax hij
  let σ := occupancy B.p θ/(N:ℝ)
  let υ := occupancy B.m θ/(N:ℝ)
  obtain ⟨hσ,hυ⟩ := actual_occupancy_box hN B θ
  change σ ∈ Icc 0 1 at hσ
  change υ ∈ Icc 0 1 at hυ
  let m := θ i+d.b
  let M := θ j+d.b
  let E := ε+τ*σ
  let x := m+E
  let y := M+E
  have hm : 0 ≤ m := by dsimp [m]; linarith [(hθ i).1]
  have hM : 0 ≤ M := by dsimp [M]; linarith [(hθ j).1]
  have hmM : m < M := by dsimp [m,M]; linarith
  have hMR : M ≤ d.b+B.delta := by dsimp [M]; linarith [(hθ j).2]
  have hδ : 0 ≤ τ*σ := mul_nonneg hτ hσ.1
  have hδτ : τ*σ ≤ τ := by nlinarith [mul_le_mul_of_nonneg_left hσ.2 hτ]
  have hE : 0 < E := by dsimp [E]; positivity
  have hx : 0 < x := by dsimp [x]; positivity
  have hy : 0 < y := by dsimp [y]; positivity
  have hxy : x < y := by dsimp [x,y]; linarith
  have hyR : y ≤ R := by
    dsimp [y,E,R]
    linarith [hεr.trans_le hε01,hτr.trans_le hτ01]
  have hxyR : x ≤ R := hxy.le.trans hyR
  have hd : θ j-θ i = y-x := by dsimp [x,y,m,M]; ring
  let L := 2*(y-x)/(Real.sqrt x*Real.sqrt y*(Real.sqrt x+Real.sqrt y))
  have hL : 0 < L := by dsimp [L]; positivity
  let base := fixedOccupancySlope d B ε τ σ υ m-fixedOccupancySlope d B ε τ σ υ M
  let err := actualOccupancyCorrection d B ε τ θ i j
  have hbase : k*L ≤ (preferredCompactDirection*base).re := by
    have h := hgap ε τ σ υ m M hε (hεr.trans_le hε0g) hτ (hτr.trans_le hτ0g)
      hσ hυ hm hmM.le hMR
    simpa only [L,base,x,y,E,add_assoc,add_sub_add_right_eq_sub] using h
  have hsl (v : Fin N) : ‖actualBumpSlopeVector d B ε τ θ v‖ ≤
      A/Real.sqrt ((θ v+d.b)+E) := by
    have hu : 0 ≤ θ v+d.b := by linarith [(hθ v).1]
    have huR : θ v+d.b ≤ d.b+B.delta := by linarith [(hθ v).2]
    have h := (hsource ε τ σ υ (θ v+d.b) hε (hεr.trans_le hε0s) hτ
      (hτr.trans_le hτ0s) hσ hυ hu huR).2
    simpa only [actualBumpSlopeVector,σ,υ,E,show -d.b+(θ v+d.b) = θ v by ring,add_assoc] using h
  have hslmin (v : Fin N) : ‖actualBumpSlopeVector d B ε τ θ v‖ ≤ A/Real.sqrt x := by
    have huv : x ≤ (θ v+d.b)+E := by dsimp [x,m]; linarith [hmin v]
    exact (hsl v).trans (div_le_div₀ hA.le le_rfl (Real.sqrt_pos.mpr hx) (Real.sqrt_le_sqrt huv))
  have herr : ‖err‖ ≤ k*L/2 := by
    have he := herror N hN ε τ hτ θ i j (hθ i) (hθ j) hij.le
      (A/Real.sqrt x) (by positivity) hslmin
    have hscale := occupancy_correction_scale hx hxy.le hyR
    change (y-x)/Real.sqrt x ≤ R*L at hscale
    have hsmall : τ*(4*K*A*R) ≤ k :=
      (le_div_iff₀ (by positivity : 0 < 4*K*A*R)).mp (hτr.trans_le hτ0abs).le
    change ‖err‖ ≤ _ at he
    rw [hd] at he
    calc
      ‖err‖ ≤ 2*τ*K*(y-x)*(A/Real.sqrt x) := he
      _ = (2*τ*K*A)*((y-x)/Real.sqrt x) := by ring
      _ ≤ (2*τ*K*A)*(R*L) := mul_le_mul_of_nonneg_left hscale (by positivity)
      _ ≤ k*L/2 := by nlinarith [mul_le_mul_of_nonneg_right hsmall hL.le]
  have habs := oblique_correction_absorption hk hL preferredCompactDirection_norm.le hbase herr
  have hD : actualExtremeProjection d B ε τ θ i j = (preferredCompactDirection*(base+err)).re := by
    unfold actualExtremeProjection
    rw [actual_extreme_phase_derivative hN d B hε hτ θ i j]
  have hDpos : 0 < actualExtremeProjection d B ε τ θ i j := by rw [hD]; exact habs.2
  have hDlower : (k/2)*L ≤ actualExtremeProjection d B ε τ θ i j := by
    rw [hD]
    nlinarith [habs.1]
  have hi' : ‖actualBumpSlopeVector d B ε τ θ i+1‖ ≤ A'/Real.sqrt x :=
    shifted_slope_bound hx hxyR (hsl i)
  have hj' : ‖actualBumpSlopeVector d B ε τ θ j+1‖ ≤ A'/Real.sqrt y :=
    shifted_slope_bound hy hyR (hsl j)
  have hnum : ‖(actualBumpSlopeVector d B ε τ θ i+1)*(actualBumpSlopeVector d B ε τ θ j+1)‖ ≤
      A'^2/(Real.sqrt x*Real.sqrt y) := by
    rw [norm_mul]
    calc
      _ ≤ (A'/Real.sqrt x)*(A'/Real.sqrt y) := mul_le_mul hi' hj' (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have hratio := extreme_jacobian_ratio hx hxy (by positivity : 0 < k/2)
    (sq_nonneg A') hnum hDlower
  have henergy := actual_occupancy_energy_comparison hN (p := fun v => B.p (θ v))
    (u := fun v => θ v+d.b) d.b_pos hτ hε.le hM
    (fun v => B.lower_bound (θ v)) (fun v => B.upper_bound (θ v))
    (by intro v; dsimp [M]; linarith [hmax v])
    (by
      intro v hpv
      have hvp : θ v ∈ Icc (-Real.pi) Real.pi := by
        constructor <;> linarith [(hθ v).1,(hθ v).2,d.b_lt,B.delta_b,d.b_pos]
      have hθp := (B.upper_support (θ v) hvp (ne_of_gt hpv)).1
      linarith)
  change E ≤ (1+τ/d.b)*(M+ε) at henergy
  have ht1 : τ ≤ 1 := (hτr.trans_le hτ01).le
  have htb : τ/d.b ≤ 1/d.b := div_le_div_of_nonneg_right ht1 d.b_pos.le
  have he' : E ≤ (1+1/d.b)*(M+ε) := henergy.trans
    (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
  have hyscale : y ≤ Ce*(M+ε) := by dsimp only [y,Ce]; nlinarith only [he',hε]
  have hsqrt := Real.sqrt_le_sqrt hyscale
  rw [Real.sqrt_mul hCe.le] at hsqrt
  refine ⟨hDpos,?_⟩
  calc
    _ ≤ (A'^2/(k/2))*Real.sqrt y/(y-x) := hratio
    _ ≤ (A'^2/(k/2))*(Real.sqrt Ce*Real.sqrt (M+ε))/(y-x) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsqrt (by positivity))
        (sub_nonneg.mpr hxy.le)
    _ = C*Real.sqrt (θ j+d.b+ε)/(θ j-θ i) := by rw [hd]; dsimp [C,M]; ring

/-- The literal manuscript G1 proposition now follows for every genuine
source bump, with the constrained path and all actual occupancies retained. -/
theorem preferred_extreme_coarea (d : PreferredBranchData) (B : PreferredCoareaBump d) :
    PreferredExtremeCoareaStatement d B := by
  obtain ⟨C,ε0,τ0,hC,hε0,hτ0,hestimate⟩ := preferred_actual_extreme_estimate d B
  refine ⟨C,τ0,ε0,B.delta/2,hC,hτ0,hε0,by exact div_pos B.delta_pos (by norm_num),by linarith [B.delta_pos],?_⟩
  intro τ hτ hτr N hN ε hε hεr θ hθ _ i j hext hmin hij
  have hNpos : 0 < N := by omega
  have hright (v : Fin N) : θ v ∈ Icc (-d.b) B.delta :=
    ⟨by linarith [(hext v).1],(hθ v).2⟩
  have h := hestimate N hNpos ε τ hε hεr hτ.le hτr θ hright i j
    (fun v => (hext v).1) (fun v => (hext v).2) hij
  have hi := (actual_bump_phase_hasDerivAt hNpos d B hε hτ.le θ i).deriv
  have hj := (actual_bump_phase_hasDerivAt hNpos d B hε hτ.le θ j).deriv
  dsimp only
  rw [hi,hj]
  exact h

end
end IsingBulk.Preferred22
