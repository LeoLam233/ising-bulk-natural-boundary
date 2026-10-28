import IsingBulk.HT22.Geometry.FiniteEqualityCover
import IsingBulk.Preferred22.FiniteEquality
import IsingBulk.HT22.First.LocalLimit.NonresonantArithmetic

namespace IsingBulk.HT22.Geometry
noncomputable section
open Complex IsingBulk.PrimeFamily Arithmetic LocalLimit

theorem signedEqualityMean_injective (negative : Bool) {N : ℕ} (hN : 0<N) :
    Function.Injective (signedEqualityMean negative N) := by
  intro l m he
  have hNr : (N:ℝ)≠0 := by exact_mod_cast hN.ne'
  unfold signedEqualityMean at he
  have hh := congrArg (fun x : ℝ => x*(N:ℝ)) he
  simp only [div_mul_cancel₀ _ hNr] at hh
  have hlm : (l:ℝ)=(m:ℝ) := by nlinarith [Real.pi_pos]
  exact_mod_cast hlm

/-- A literal signed product resonance determines the actual affine signed
integer phase, with no unsigned constraint silently imposed. -/
theorem signed_resonance_eq_mean (negative : Bool) {N : ℕ} (hN : 0<N) {β : ℝ}
    (hres : Physical.constraintSign negative*(exp (-(β:ℂ)*I))^N=1) :
    ∃ m : ℤ, β=signedEqualityMean negative N m := by
  rw [signed_mean_phase_identity negative hN 0 β] at hres
  have he : exp (-(N:ℂ)*((β+signedEqualityMean negative N 0:ℝ):ℂ)*I)=1 := by
    simpa only [ofReal_add] using hres
  obtain ⟨m,hm⟩ := resonance_eq_angle hN he
  have hNr : (N:ℝ)≠0 := by exact_mod_cast hN.ne'
  cases negative
  · refine ⟨m,?_⟩
    simpa only [signedEqualityMean,Physical.constraintAngle,Bool.false_eq_true,↓reduceIte,
      Int.cast_zero,mul_zero,zero_add,zero_div,add_zero,angle] using hm
  · refine ⟨m-1,?_⟩
    simp only [signedEqualityMean,Physical.constraintAngle,↓reduceIte,Int.cast_zero,mul_zero,zero_add,angle] at hm ⊢
    push_cast
    apply (eq_div_iff hNr).mpr
    have hh := (eq_div_iff hNr).mp hm
    field_simp at hh
    field_simp
    nlinarith

/-- Signed equal-angle resonances produce the original Nickel equation
at the prescribed selected root in either upper quadrant. -/
theorem signed_equality_implies_original_nickel {p N : ℕ} {a l : ℤ}
    (hN : 0<N) (hodd : Odd N) (negative : Bool) (β : ℝ)
    (hlevel : Real.cos (signedEqualityMean negative N l)+Real.cos β =
      if negative then -(2*Real.cos (angle p a)) else 2*Real.cos (angle p a))
    (hres : Physical.constraintSign negative*(exp (-(β:ℂ)*I))^N=1) :
    NickelAt (angleRoot p a) N := by
  obtain ⟨m,hm⟩ := signed_resonance_eq_mean negative hN hres
  rw [hm] at hlevel
  have htrace := exp_angle_add_inv (angle p a)
  change angleRoot p a+(angleRoot p a)⁻¹=2*(Real.cos (angle p a):ℂ) at htrace
  cases negative
  · refine ⟨norm_exp_ofReal_mul_I _,l,m,?_⟩
    simp only [signedEqualityMean,Physical.constraintAngle,Bool.false_eq_true,↓reduceIte,add_zero] at hlevel
    rw [htrace]
    exact_mod_cast hlevel.symm
  · rw [←neg_neg (angleRoot p a)]
    apply (signedNickel_iff_neg hodd (-angleRoot p a)).mp
    refine ⟨by simp [angleRoot],l,m,?_⟩
    rw [inv_neg]
    have he : -angleRoot p a+ -(angleRoot p a)⁻¹= -(angleRoot p a+(angleRoot p a)⁻¹) := by ring
    rw [he,htrace]
    simp only [signedEqualityMean,Physical.constraintAngle,↓reduceIte] at hlevel
    exact_mod_cast hlevel.symm

/-- Every actual signed equality center at lower odd order has the
nonzero physical denominator required by the local analytic extension. -/
theorem lower_signed_equality_product_gap {p N : ℕ} (hp : p.Prime) (hp5 : 5≤p)
    {a : ℤ} (ha : PrimeIndex p a) (hN : 0<N) (hodd : Odd N) (hNp : N<p)
    (negative : Bool) (l : ℤ) (β : ℝ)
    (hlevel : Real.cos (signedEqualityMean negative N l)+Real.cos β =
      if negative then -(2*Real.cos (angle p a)) else 2*Real.cos (angle p a)) :
    1-Physical.constraintSign negative*(exp (-(β:ℂ)*I))^N≠0 := by
  intro hz
  have hr := (sub_eq_zero.mp hz).symm
  exact (primeRoot_first_order hp hp5 ha).2.2 N hN hNp
    (signed_equality_implies_original_nickel hN hodd negative β hlevel hr)

/-- At the first order the only signed resonance has the prescribed
critical cosine; no extra equality centers are admitted. -/
theorem first_signed_equality_cosine {p : ℕ} (hp : p.Prime) (hp5 : 5≤p)
    {a : ℤ} (ha : PrimeIndex p a) (negative : Bool) (l : ℤ) (β : ℝ)
    (hlevel : Real.cos (signedEqualityMean negative p l)+Real.cos β =
      if negative then -(2*Real.cos (angle p a)) else 2*Real.cos (angle p a))
    (hres : Physical.constraintSign negative*(exp (-(β:ℂ)*I))^p=1) :
    Real.cos (signedEqualityMean negative p l)=
      if negative then -Real.cos (angle p a) else Real.cos (angle p a) := by
  obtain ⟨m,hm⟩ := signed_resonance_eq_mean negative hp.pos hres
  rw [hm] at hlevel
  have htrace := exp_angle_add_inv (angle p a)
  change angleRoot p a+(angleRoot p a)⁻¹=2*(Real.cos (angle p a):ℂ) at htrace
  cases negative
  · have he : angleRoot p a+(angleRoot p a)⁻¹=
        (Real.cos (angle p l):ℂ)+(Real.cos (angle p m):ℂ) := by
      rw [htrace]
      simpa only [signedEqualityMean,Physical.constraintAngle,Bool.false_eq_true,↓reduceIte,
        add_zero,angle,ofReal_mul,ofReal_ofNat,ofReal_add] using congrArg (fun x : ℝ => (x:ℂ)) hlevel.symm
    simpa only [signedEqualityMean,Physical.constraintAngle,Bool.false_eq_true,↓reduceIte,
      add_zero,angle] using (primeRoot_unique_cosine_pair hp hp5 ha l m he).1
  · obtain ⟨k,hk⟩ := hp.odd_of_ne_two (by omega)
    have hshift (j : ℤ) : signedEqualityMean true p j=angle p (j+k+1)-Real.pi := by
      rw [hk]
      exact signedAngle_shift k j
    rw [hshift,hshift,Real.cos_sub_pi,Real.cos_sub_pi] at hlevel
    simp only [↓reduceIte] at hlevel
    have he : angleRoot p a+(angleRoot p a)⁻¹=
        (Real.cos (angle p (l+k+1)):ℂ)+(Real.cos (angle p (m+k+1)):ℂ) := by
      rw [htrace]
      have hh : 2*Real.cos (angle p a)=Real.cos (angle p (l+k+1))+Real.cos (angle p (m+k+1)) := by
        simpa only [↓reduceIte] using neg_inj.mp (show -(2*Real.cos (angle p a))=
          -(Real.cos (angle p (l+k+1))+Real.cos (angle p (m+k+1))) by
            simpa only [neg_add] using hlevel.symm)
      exact_mod_cast hh
    have hc := (primeRoot_unique_cosine_pair hp hp5 ha (l+k+1) (m+k+1) he).1
    simpa only [hshift,Real.cos_sub_pi,↓reduceIte] using congrArg Neg.neg hc

theorem first_other_signed_equality_product_gap {p : ℕ} (hp : p.Prime) (hp5 : 5≤p)
    {a : ℤ} (ha : PrimeIndex p a) (negative : Bool) (l : ℤ) (β : ℝ)
    (hlevel : Real.cos (signedEqualityMean negative p l)+Real.cos β =
      if negative then -(2*Real.cos (angle p a)) else 2*Real.cos (angle p a))
    (hother : Real.cos (signedEqualityMean negative p l)≠
      if negative then -Real.cos (angle p a) else Real.cos (angle p a)) :
    1-Physical.constraintSign negative*(exp (-(β:ℂ)*I))^p≠0 := by
  intro hz
  exact hother (first_signed_equality_cosine hp hp5 ha negative l β hlevel (sub_eq_zero.mp hz).symm)

/-- On the original one-sided right interval only the lower critical
center survives; reflection supplies the other physical chart. -/
theorem first_signed_right_equality_unique {p : ℕ} (hp : p.Prime) (hp5 : 5≤p)
    {a : ℤ} (ha : PrimeIndex p a) (negative : Bool) (l : ℤ) (β : ℝ)
    (d : IsingBulk.Preferred22.PreferredBranchData)
    (B : IsingBulk.Preferred22.PreferredCoareaBump d)
    (hcos : Real.cos d.alpha=if negative then -Real.cos (angle p a) else Real.cos (angle p a))
    (hlevel : Real.cos (signedEqualityMean negative p l)+Real.cos β =
      if negative then -(2*Real.cos (angle p a)) else 2*Real.cos (angle p a))
    (hmean : signedEqualityMean negative p l∈Set.Icc (-Real.pi-B.delta) B.delta)
    (hres : Physical.constraintSign negative*(exp (-(β:ℂ)*I))^p=1) :
    signedEqualityMean negative p l= -d.alpha := by
  apply IsingBulk.Preferred22.preferred_right_equal_cosine_unique d.alpha_pos d.alpha_lt
    B.delta_pos.le B.delta_alpha hmean
  exact (first_signed_equality_cosine hp hp5 ha negative l β hlevel hres).trans hcos.symm

end
end IsingBulk.HT22.Geometry
