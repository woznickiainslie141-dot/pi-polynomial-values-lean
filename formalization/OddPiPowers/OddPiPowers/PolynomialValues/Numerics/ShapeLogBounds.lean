module

public import OddPiPowers.PolynomialValues.Analysis.OddSeriesBounds
public import OddPiPowers.PolynomialValues.Numerics.ShapeGeometry
public import Mathlib.Data.Rat.BigOperators

/-! Rational logarithmic enclosures for the initial factorial cost
and the penalty from the zero at the origin. -/

@[expose] public section

namespace PiPolynomialValues

open Real

def logArgument {K : Type*} [Field K] (x : K) := (x-1)/(x+1)
def simpleLogLo {K : Type*} [Field K] (x : K) := 2*arcOdd 1 25 (logArgument x)
def simpleLogHi {K : Type*} [Field K] (x : K) :=
  simpleLogLo x+2*(logArgument x)^51/(51*(1-(logArgument x)^2))

theorem simpleLog_bounds {x : ℝ} (hx : 1≤x) :
    simpleLogLo x ≤ log x ∧ log x ≤ simpleLogHi x := by
  let t := logArgument x
  have hxp : 0<x+1 := by linarith
  have ht : 0≤t := div_nonneg (sub_nonneg.mpr hx) hxp.le
  have ht1 : t<1 := (div_lt_one hxp).mpr (by linarith)
  have he : 2*halfLogRatio t=log x := by
    rw [halfLogRatio,← log_div (by linarith : 1+t≠0) (by linarith : 1-t≠0)]
    have hh : (1+t)/(1-t)=x := by
      apply (div_eq_iff (by linarith)).mpr
      dsimp [t,logArgument]
      field_simp [hxp.ne']
      <;> ring
    rw [hh]
    ring
  have H := halfLogRatio_odd_bounds ht ht1 25
  norm_num only [Nat.reduceMul,Nat.reduceAdd,Nat.cast_ofNat] at H
  change 2*arcOdd 1 25 t≤log x ∧ log x≤2*arcOdd 1 25 t+2*t^51/(51*(1-t^2))
  rw [mul_div_assoc]
  constructor <;> linarith only [H.1,H.2,he]

def logShift (x : ℚ) : ℕ := if x<2 then 0 else if x<4 then 1 else 2

def scaledLogLo (x : ℚ) :=
  let k := logShift x
  (k : ℚ)*simpleLogLo 2+simpleLogLo (x/2^k)
def scaledLogHi (x : ℚ) :=
  let k := logShift x
  (k : ℚ)*simpleLogHi 2+simpleLogHi (x/2^k)

theorem scaledLog_bounds (x : ℚ) (hx : 1≤x) :
    (scaledLogLo x : ℝ)≤log (x : ℝ) ∧ log (x : ℝ)≤(scaledLogHi x : ℝ) := by
  let k := logShift x
  let y := x/2^k
  have hy : 1≤y := by
    dsimp [y,k,logShift]
    split_ifs <;> norm_num at * <;> linarith
  have hlo (q : ℚ) : ((simpleLogLo q : ℚ) : ℝ)=simpleLogLo (q : ℝ) := by
    unfold simpleLogLo arcOdd logArgument
    push_cast
    rfl
  have hhi (q : ℚ) : ((simpleLogHi q : ℚ) : ℝ)=simpleLogHi (q : ℝ) := by
    unfold simpleLogHi logArgument
    push_cast [hlo]
    rfl
  have H := simpleLog_bounds (show (1:ℝ)≤(y : ℝ) by exact_mod_cast hy)
  have H₂ := simpleLog_bounds (by norm_num : (1:ℝ)≤2)
  have he : log (x : ℝ)=(k : ℝ)*log 2+log (y : ℝ) := by
    have hx' : (0:ℝ)<(x : ℝ) := by exact_mod_cast (zero_lt_one.trans_le hx)
    have he : (y : ℝ)=(x : ℝ)/(2:ℝ)^k := by dsimp [y]; push_cast; rfl
    rw [he,log_div hx'.ne' (pow_ne_zero _ (by norm_num : (2:ℝ)≠0)),log_pow]
    ring
  have hk : 0≤(k : ℝ) := Nat.cast_nonneg _
  change (((k : ℚ)*simpleLogLo 2+simpleLogLo y : ℚ) : ℝ) ≤ _ ∧
    _≤(((k : ℚ)*simpleLogHi 2+simpleLogHi y : ℚ) : ℝ)
  simp only [Rat.cast_add,Rat.cast_mul,Rat.cast_natCast,hlo,hhi,Rat.cast_ofNat]
  rw [he]
  exact ⟨add_le_add (mul_le_mul_of_nonneg_left H₂.1 hk) H.1,
    add_le_add (mul_le_mul_of_nonneg_left H₂.2 hk) H.2⟩

def logTickLo (x : ℚ) : ℚ := ((⌊10^20*scaledLogLo x⌋ : ℤ) : ℚ)/10^20
def logTickHi (x : ℚ) : ℚ := ((⌊10^20*scaledLogHi x⌋+1 : ℤ) : ℚ)/10^20

theorem logTick_bounds (x : ℚ) (hx : 1≤x) :
    (logTickLo x : ℝ)≤log (x : ℝ) ∧ log (x : ℝ)≤(logTickHi x : ℝ) := by
  have H := scaledLog_bounds x hx
  have hl : logTickLo x≤scaledLogLo x := (div_le_iff₀ (by decide)).mpr (by
    have h := Int.floor_le ((10:ℚ)^20*scaledLogLo x)
    linarith only [h])
  have hh : scaledLogHi x≤logTickHi x := (le_div_iff₀ (by decide)).mpr (by
    push_cast
    have h := Int.lt_floor_add_one ((10:ℚ)^20*scaledLogHi x)
    linarith only [h])
  exact ⟨(Rat.cast_le.mpr hl).trans H.1,H.2.trans (Rat.cast_le.mpr hh)⟩

end PiPolynomialValues
