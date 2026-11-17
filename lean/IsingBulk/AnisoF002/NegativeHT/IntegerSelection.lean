import IsingBulk.AnisoF002.NegativeHT.FactorialRectangle

/-!
# Integer-order selection and exact recurrence bounds

The first crossing is selected on natural derivative orders. No real
interpolation of j is introduced. The signs at the two endpoints and the
physical tau estimates remain separate obligations.
-/

namespace IsingBulk.AnisoF002.NegativeHT

/-- An exact integer first crossing overshoots by at most one bounded step.
No monotonicity or interpolation hypothesis is needed for this conclusion. -/
theorem exists_small_nonnegative_crossing (F : ℕ → ℝ)
    (start finish : ℕ) (δ : ℝ) (hsf : start ≤ finish)
    (hstart : F start < 0) (hfinish : 0 ≤ F finish)
    (hstep : ∀ j, start ≤ j → j < finish → F (j+1)-F j ≤ δ) :
    ∃ j, start < j ∧ j ≤ finish ∧ 0 ≤ F j ∧ F j ≤ δ := by
  have hex : ∃ k : ℕ, 0 ≤ F (start+k) := by
    refine ⟨finish-start, ?_⟩
    simpa [Nat.add_sub_of_le hsf] using hfinish
  let k := Nat.find hex
  have hk : 0 ≤ F (start+k) := Nat.find_spec hex
  have hbound : k ≤ finish-start := by
    apply Nat.find_min'
    simpa [Nat.add_sub_of_le hsf] using hfinish
  have hkpos : 0<k := by
    by_contra hn
    have he : k=0 := by omega
    simp only [he, Nat.add_zero] at hk
    linarith
  have hprev : F (start+(k-1)) < 0 := by
    have hm := Nat.find_min hex (show k-1<k by omega)
    exact lt_of_not_ge hm
  have hst : start ≤ start+(k-1) := by omega
  have hfn : start+(k-1) < finish := by omega
  have hc := hstep (start+(k-1)) hst hfn
  have he : start+(k-1)+1 = start+k := by omega
  rw [he] at hc
  refine ⟨start+k, by omega, by omega, hk, ?_⟩
  linarith

/-- Exact bounds for the logarithm in the gamma-ratio step. -/
theorem log_gamma_step_bounds (J a b : ℝ) (hab : a≤b) (hb : b<J) :
    -((b-a)/(J-b)) ≤ Real.log ((J-b)/(J-a)) ∧
      Real.log ((J-b)/(J-a)) ≤ 0 := by
  have hxb : 0<J-b := by linarith
  have hxa : 0<J-a := by linarith
  have h := log_increment_bounds hxb (show 0≤b-a by linarith)
  have he : J-b+(b-a) = J-a := by ring
  rw [he] at h
  rw [Real.log_div hxb.ne' hxa.ne']
  constructor <;> linarith [h.1, h.2]

/-- Applying the exact-factor logarithmic recurrence gives explicit lower
and upper bounds for each integer step of the neighboring-particle comparison. -/
theorem centered_order_increment_bounds
    (l r j : ℕ) (Bl hl sl τl Br hr sr τr : ℝ)
    (hln : 0<l) (hlB : 0<Bl) (hlh : 0<hl) (hls : 0<sl) (hlτ : 0<τl)
    (hrn : 0<r) (hrB : 0<Br) (hrh : 0<hr) (hrs : 0<sr) (hrτ : 0<τr)
    (halr : particleExponent l ≤ particleExponent r)
    (hra : particleExponent r ≤ j) :
    let Δ := (Real.log (modelMagnitude r (j+1) Br hr sr τr) -
       Real.log (modelMagnitude l (j+1) Bl hl sl τl)) -
      (Real.log (modelMagnitude r j Br hr sr τr) -
       Real.log (modelMagnitude l j Bl hl sl τl))
    Real.log (τl/τr) -
      ((particleExponent r:ℝ)-particleExponent l) /
        (((j+1:ℕ):ℝ)-particleExponent r) ≤ Δ ∧
      Δ ≤ Real.log (τl/τr) := by
  have hla : particleExponent l ≤ j := halr.trans hra
  have hrec := centered_log_ratio_order_step l r j Bl hl sl τl Br hr sr τr
    hln hlB hlh hls hlτ hrn hrB hrh hrs hrτ hla hra
  have hab : (particleExponent l:ℝ) ≤ particleExponent r := by exact_mod_cast halr
  have hb : (particleExponent r:ℝ) < ((j+1:ℕ):ℝ) := by
    exact_mod_cast (show particleExponent r < j+1 by omega)
  have h := log_gamma_step_bounds ((j+1:ℕ):ℝ) (particleExponent l) (particleExponent r) hab hb
  dsimp only
  rw [hrec]
  constructor <;> linarith [h.1, h.2]

end IsingBulk.AnisoF002.NegativeHT
