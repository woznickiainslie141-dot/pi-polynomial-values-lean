module

public import OddPiPowers.PolynomialValues.Numerics.Certificates.Stripes.Group000
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Stripes.Group001
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Stripes.Group005
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Stripes.Group009
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Stripes.Group013
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Stripes.Group017
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Stripes.Group021
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Stripes.Group025
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Stripes.Group029
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Stripes.Group033
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Stripes.Group037
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Stripes.Group041
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Stripes.Group045
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Stripes.Group049
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Stripes.Group053
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Stripes.Group057
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Stripes.Group061
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Stripes.Group065
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Stripes.Group069
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Stripes.Group073
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Stripes.Group077
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Stripes.Group081
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Stripes.Group085
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Stripes.Group089
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Stripes.Group093
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Stripes.Group097
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Stripes.Group101
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Stripes.Group105
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Stripes.Group109
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Stripes.Group113
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Stripes.Group117
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Stripes.Group121

@[expose] public section

namespace PiPolynomialValues.Certificates

set_option maxRecDepth 8192 in
def spatialBasis : (r : ℕ) → StripeBasis r
  | 0 => basis000
  | 1 => basis001
  | 2 => basis002
  | 3 => basis003
  | 4 => basis004
  | 5 => basis005
  | 6 => basis006
  | 7 => basis007
  | 8 => basis008
  | 9 => basis009
  | 10 => basis010
  | 11 => basis011
  | 12 => basis012
  | 13 => basis013
  | 14 => basis014
  | 15 => basis015
  | 16 => basis016
  | 17 => basis017
  | 18 => basis018
  | 19 => basis019
  | 20 => basis020
  | 21 => basis021
  | 22 => basis022
  | 23 => basis023
  | 24 => basis024
  | 25 => basis025
  | 26 => basis026
  | 27 => basis027
  | 28 => basis028
  | 29 => basis029
  | 30 => basis030
  | 31 => basis031
  | 32 => basis032
  | 33 => basis033
  | 34 => basis034
  | 35 => basis035
  | 36 => basis036
  | 37 => basis037
  | 38 => basis038
  | 39 => basis039
  | 40 => basis040
  | 41 => basis041
  | 42 => basis042
  | 43 => basis043
  | 44 => basis044
  | 45 => basis045
  | 46 => basis046
  | 47 => basis047
  | 48 => basis048
  | 49 => basis049
  | 50 => basis050
  | 51 => basis051
  | 52 => basis052
  | 53 => basis053
  | 54 => basis054
  | 55 => basis055
  | 56 => basis056
  | 57 => basis057
  | 58 => basis058
  | 59 => basis059
  | 60 => basis060
  | 61 => basis061
  | 62 => basis062
  | 63 => basis063
  | 64 => basis064
  | 65 => basis065
  | 66 => basis066
  | 67 => basis067
  | 68 => basis068
  | 69 => basis069
  | 70 => basis070
  | 71 => basis071
  | 72 => basis072
  | 73 => basis073
  | 74 => basis074
  | 75 => basis075
  | 76 => basis076
  | 77 => basis077
  | 78 => basis078
  | 79 => basis079
  | 80 => basis080
  | 81 => basis081
  | 82 => basis082
  | 83 => basis083
  | 84 => basis084
  | 85 => basis085
  | 86 => basis086
  | 87 => basis087
  | 88 => basis088
  | 89 => basis089
  | 90 => basis090
  | 91 => basis091
  | 92 => basis092
  | 93 => basis093
  | 94 => basis094
  | 95 => basis095
  | 96 => basis096
  | 97 => basis097
  | 98 => basis098
  | 99 => basis099
  | 100 => basis100
  | 101 => basis101
  | 102 => basis102
  | 103 => basis103
  | 104 => basis104
  | 105 => basis105
  | 106 => basis106
  | 107 => basis107
  | 108 => basis108
  | 109 => basis109
  | 110 => basis110
  | 111 => basis111
  | 112 => basis112
  | 113 => basis113
  | 114 => basis114
  | 115 => basis115
  | 116 => basis116
  | 117 => basis117
  | 118 => basis118
  | 119 => basis119
  | 120 => basis120
  | 121 => basis121
  | 122 => basis122
  | 123 => basis123
  | 124 => basis124
  | r+125 => ⟨packEval spatialBase (stripeSize (r+125)) (stripeSample (r+125)), rfl⟩

end PiPolynomialValues.Certificates
