import IsingBulk.Anisotropic.RegularEdges.OddRadialBounds

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace IsingBulk.Anisotropic.RegularEdges

def oddRadialPrimitive (m : ℕ) (Q c : ℂ) (r : ℝ) : ℂ :=
  ((r:ℂ)^2/(Q+c*(r:ℂ)^2))^(m+1)/(2*(m+1:ℕ)*Q)

theorem oddRadialPrimitive_hasDerivAt (m : ℕ) {Q c : ℂ}
    (hQ : 0<Q.re) (hc : 0<c.re) (r : ℝ) :
    HasDerivAt (oddRadialPrimitive m Q c) (oddRadialKernel m Q c r) r := by
  have hq : Q≠0 := by intro h; simp [h] at hQ
  have hn : (m+1:ℕ)≠0 := by omega
  have hn' : ((m+1:ℕ):ℂ)≠0 := Nat.cast_ne_zero.mpr hn
  have hd := oddQuadratic_ne_zero hQ hc r
  have hz := (hasDerivAt_id (r:ℂ)).pow 2
  have hf := ((hz.div ((hz.const_mul c).const_add Q) hd).pow (m+1)).div_const
    (2*((m+1:ℕ):ℂ)*Q)
  have he : HasDerivAt (fun z : ℂ => (z^2/(Q+c*z^2))^(m+1)/(2*((m+1:ℕ):ℂ)*Q))
      (oddRadialKernel m Q c r) (r:ℂ) := by
    convert hf using 1
    · rfl
    · simp only [oddRadialKernel,Pi.pow_apply,Pi.div_apply,id_eq,Nat.add_sub_cancel,
        Nat.reduceSub,pow_one,mul_one,Nat.cast_ofNat,div_pow]
      field_simp [hd,hq,hn']
      simp only [pow_add,pow_mul,pow_one]
      ring
  exact he.comp_ofReal

theorem oddRadialPrimitive_tendsto (m : ℕ) {Q c : ℂ}
    (_hQ : 0<Q.re) (hc : 0<c.re) :
    Tendsto (oddRadialPrimitive m Q c) atTop (𝓝 (1/(2*((m+1:ℕ):ℂ)*Q*c^(m+1)))) := by
  have hc0 : c≠0 := by intro h; simp [h] at hc
  have hi : Tendsto (fun r : ℝ => (r:ℂ)⁻¹) atTop (𝓝 (0:ℂ)) := by
    simpa only [Function.comp_def,Complex.ofReal_inv,Complex.ofReal_zero] using Complex.continuous_ofReal.continuousAt.tendsto.comp tendsto_inv_atTop_zero
  have hlim : Tendsto (fun r : ℝ => (Q*((r:ℂ)⁻¹)^2+c)⁻¹) atTop (𝓝 c⁻¹) := by
    have hh : Tendsto (fun r : ℝ => Q*((r:ℂ)⁻¹)^2+c) atTop (𝓝 c) := by
      simpa using (tendsto_const_nhds (x:=Q) |>.mul (hi.pow 2)).add (tendsto_const_nhds (x:=c))
    exact hh.inv₀ hc0
  have he : (fun r : ℝ => (r:ℂ)^2/(Q+c*(r:ℂ)^2)) =ᶠ[atTop]
      (fun r : ℝ => (Q*((r:ℂ)⁻¹)^2+c)⁻¹) := by
    filter_upwards [eventually_gt_atTop (0:ℝ)] with r hr
    have hr0 : (r:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hr.ne'
    rw [inv_pow,←div_eq_mul_inv,div_add' _ _ _ (pow_ne_zero 2 hr0),inv_div]
  have ht := (hlim.congr' he.symm).pow (m+1) |>.div_const (2*((m+1:ℕ):ℂ)*Q)
  convert ht using 1
  · rfl
  · congr 1
    simp only [inv_pow,div_eq_mul_inv,mul_inv_rev,one_mul]

end IsingBulk.Anisotropic.RegularEdges
