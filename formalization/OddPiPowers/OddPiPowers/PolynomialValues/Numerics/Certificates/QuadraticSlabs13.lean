module

public import OddPiPowers.PolynomialValues.Numerics.PrimeBoxSegment

@[expose] public section

namespace PiPolynomialValues.PrimeWindow

open FourPeriod

def quadraticSlabs13 : List Slab := [
   ⟨⟨57000, 919⟩, ⟨68125, 1097⟩, [⟨⟨8119, -100⟩, ⟨-9433, 118⟩, -1, 1, 30679330773⟩]⟩,
   ⟨⟨14372680000, 224843709⟩, ⟨4575792, 71447⟩, [⟨⟨6632, -84⟩, ⟨0, 1⟩, -1, 1, 42877634453⟩]⟩,
   ⟨⟨500000, 7741⟩, ⟨610000, 9433⟩, [⟨⟨0, 0⟩, ⟨-9433, 122⟩, -1, 2, 27864378203⟩]⟩,
   ⟨⟨4898444, 71447⟩, ⟨76000, 1107⟩, [⟨⟨-5535, 76⟩, ⟨-5810, 80⟩, -1, 1, 45910901268⟩]⟩,
   ⟨⟨156000, 2269⟩, ⟨151250, 2197⟩, [⟨⟨-4595, 64⟩, ⟨8788, -120⟩, 1, 1, 28492077553⟩]⟩,
   ⟨⟨16572580000, 224843709⟩, ⟨65000, 881⟩, [⟨⟨0, 0⟩, ⟨-6632, 98⟩, -1, 2, 47364956967⟩]⟩,
   ⟨⟨45171280000, 612086449⟩, ⟨110000, 1489⟩, [⟨⟨0, 0⟩, ⟨-6632, 98⟩, -1, 4, 33219078185⟩]⟩,
   ⟨⟨120000, 1487⟩, ⟨5778404, 71447⟩, [⟨⟨-6632, 108⟩, ⟨0, 1⟩, 1, 1, 37010854279⟩]⟩]

theorem quadraticSlabs13_checked :
    CheckedSlabs quadraticShape ⟨4546460000, 74947903⟩ ⟨5778404, 71447⟩ quadraticSlabs13 8 293419211681 := by
  constructor <;> decide +kernel

end PiPolynomialValues.PrimeWindow
