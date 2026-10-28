import IsingBulk.HT22.Arithmetic.PrimeRoot

/-! Exact half-period index conversion, before any analytic continuation. -/
namespace IsingBulk.HT22.Arithmetic
noncomputable section
open IsingBulk.PrimeFamily

def signedAngle (n : ℕ) (l : ℤ) : ℝ := (2*Real.pi*l+Real.pi)/n

def SignedNickelAt (s : ℂ) (n : ℕ) : Prop :=
  ‖s‖=1 ∧ ∃ l m : ℤ, s+s⁻¹=
    (Real.cos (signedAngle n l):ℂ)+(Real.cos (signedAngle n m):ℂ)

theorem signedAngle_shift (k : ℕ) (l : ℤ) :
    signedAngle (2*k+1) l = angle (2*k+1) (l+k+1)-Real.pi := by
  unfold signedAngle angle
  push_cast
  have hn : (2*(k:ℝ)+1)≠0 := by positivity
  field_simp
  ring

/-- Adding pi to both shifted angles gives the ordinary odd-order equation
at the opposite level; integer indices are exhibited in both directions. -/
theorem signedNickel_iff_neg {n : ℕ} (hn : Odd n) (s : ℂ) :
    SignedNickelAt s n ↔ NickelAt (-s) n := by
  obtain ⟨k,rfl⟩ := hn
  constructor
  · rintro ⟨hnorm,l,m,he⟩
    refine ⟨by simpa only [norm_neg] using hnorm,l+k+1,m+k+1,?_⟩
    simp only [signedAngle_shift,Real.cos_sub_pi,Complex.ofReal_neg] at he
    rw [inv_neg]
    linear_combination -he
  · rintro ⟨hnorm,l,m,he⟩
    refine ⟨by simpa only [norm_neg] using hnorm,l-k-1,m-k-1,?_⟩
    rw [signedAngle_shift,signedAngle_shift]
    simp only [Real.cos_sub_pi,Complex.ofReal_neg]
    have hl : l-(k:ℤ)-1+k+1=l := by ring
    have hm : m-(k:ℤ)-1+k+1=m := by ring
    rw [hl,hm]
    rw [inv_neg] at he
    linear_combination -he

theorem nickelAt_star_iff (s : ℂ) (n : ℕ) : NickelAt (star s) n ↔ NickelAt s n := by
  constructor
  · rintro ⟨hnorm,l,m,he⟩
    refine ⟨by simpa only [norm_star] using hnorm,l,m,?_⟩
    have h := congrArg (fun z : ℂ => star z) he
    simp only [star_add,star_inv₀,star_star] at h
    simpa only [Complex.star_def,Complex.conj_ofReal] using h
  · rintro ⟨hnorm,l,m,he⟩
    refine ⟨by simpa only [norm_star] using hnorm,l,m,?_⟩
    have h := congrArg (fun z : ℂ => star z) he
    simp only [star_add,star_inv₀] at h
    simpa only [Complex.star_def,Complex.conj_ofReal] using h

/-- Precisely the reflected point `-conj t` used for negative upper-half data. -/
theorem signedNickel_reflected_iff {n : ℕ} (hn : Odd n) (s : ℂ) :
    SignedNickelAt (-star s) n ↔ NickelAt s n := by
  rw [signedNickel_iff_neg hn,neg_neg,nickelAt_star_iff]

/-- A prime-family root on either upper quadrant yields first signed order p
at its negation, without importing an old HT singularity theorem. -/
theorem primeRoot_first_signed_order {p : ℕ} (hp : p.Prime) (hp5 : 5≤p)
    {a : ℤ} (ha : PrimeIndex p a) :
    SignedNickelAt (-angleRoot p a) p ∧
      ∀ n : ℕ, 0<n → Odd n → n<p → ¬ SignedNickelAt (-angleRoot p a) n := by
  obtain ⟨hodd,hfirst,hlow⟩ := primeRoot_first_order hp hp5 ha
  constructor
  · rw [signedNickel_iff_neg hodd,neg_neg]
    exact hfirst
  · intro n hn hno hnp h
    apply hlow n hn hnp
    simpa only [neg_neg] using (signedNickel_iff_neg hno (-angleRoot p a)).mp h

end
end IsingBulk.HT22.Arithmetic
