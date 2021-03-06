// This program previously led to an exeption in
// PresburgerTools.nonDNFEnumDisjuncts

import ap._
import ap.parser._
import ap.basetypes.IdealInt

SimpleAPI.withProver(tightFunctionScopes = true, genTotalityAxioms = false) { p =>
import p._
import IExpression._
{


 
val P0 = createConstant("P0")
val P2 = createConstant("P2")
val P1 = createConstant("P1")
val P3 = createConstant("P3")
val P4 = createConstant("P4")
val P5 = createConstant("P5")
val P7 = createConstant("P7")
val P6 = createConstant("P6")
val P11 = createConstant("P11")
val P10 = createConstant("P10")
val P9 = createConstant("P9")
val P12 = createConstant("P12")
val P13 = createConstant("P13")
val P8 = createConstant("P8")
val P14 = createConstant("P14")
val P15 = createConstant("P15")
val P17 = createConstant("P17")
val P16 = createConstant("P16")
val P19 = createConstant("P19")
val P18 = createConstant("P18")
val P21 = createConstant("P21")
val P20 = createConstant("P20")
val P23 = createConstant("P23")
val P22 = createConstant("P22")
val P25 = createConstant("P25")
val P24 = createConstant("P24")
val P27 = createConstant("P27")
val P26 = createConstant("P26")
val P29 = createConstant("P29")
val P28 = createConstant("P28")
val P31 = createConstant("P31")
val P30 = createConstant("P30")

println(
PresburgerTools.nonDNFEnumDisjuncts(asConjunction(
!(((((((((P0 === 0) & (!(P2 === 0) & ((P1 === 0) & (!(P3 === 0) & (!(P4 === 0) & ((P5 === 0) & ((P7 === 0) & (P6 === 0)))))))) & (((((((((((((((!(P11 === 0) | !(P10 === 0)) | !(P9 === 0)) | (P12 === 0)) | (P13 === 0)) | !(P8 === 0)) | (P14 === 0)) | !(P15 === 0)) | !((P17 + -1 * P16) === 0)) | !((P19 + -1 * P18) === 0)) | !((P21 + -1 * P20) === 0)) | !((P23 + -1 * P22) === 0)) | !((P25 + -1 * P24) === 0)) | !((P27 + -1 * P26) === 0)) | !((P29 + -1 * P28) === 0)) | !((P31 + -1 * P30) === 0))) | (((P0 === 0) & (!(P2 === 0) & ((P1 === 0) & (!(P3 === 0) & (!(P4 === 0) & ((P5 === 0) & ((P7 === 0) & !(P6 === 0)))))))) & (!((P31 + -1 * P30) === 0) | (!((P29 + -1 * P28) === 0) | (!((P27 + -1 * P26) === 0) | (!((P25 + -1 * P24) === 0) | (!((P23 + -1 * P22) === 0) | (!((P21 + -1 * P20) === 0) | (!((P19 + -1 * P18) === 0) | (!((P17 + -1 * P16) === 0) | (!(P15 === 0) | ((P14 === 0) | (!(P8 === 0) | ((P13 === 0) | ((P12 === 0) | (!(P9 === 0) | (!(P10 === 0) | (P11 === 0)))))))))))))))))) | (((P0 === 0) & (!(P2 === 0) & ((P1 === 0) & (!(P3 === 0) & (!(P4 === 0) & ((!(P7 === 0) & (P6 === 0)) & (P5 === 0))))))) & (!((P31 + -1 * P30) === 0) | (!((P29 + -1 * P28) === 0) | (!((P27 + -1 * P26) === 0) | (!((P25 + -1 * P24) === 0) | (!((P23 + -1 * P22) === 0) | (!((P21 + -1 * P20) === 0) | (!((P19 + -1 * P18) === 0) | (!((P17 + -1 * P16) === 0) | (!(P15 === 0) | ((P14 === 0) | (!(P8 === 0) | ((P13 === 0) | ((P12 === 0) | (!(P9 === 0) | (!(P11 === 0) | (P10 === 0)))))))))))))))))) | (((P0 === 0) & (!(P2 === 0) & ((P1 === 0) & (!(P3 === 0) & (!(P4 === 0) & ((P5 === 0) & (!(P7 === 0) & !(P6 === 0)))))))) & (!((P31 + -1 * P30) === 0) | (!((P29 + -1 * P28) === 0) | (!((P27 + -1 * P26) === 0) | (!((P25 + -1 * P24) === 0) | (!((P23 + -1 * P22) === 0) | (!((P21 + -1 * P20) === 0) | (!((P19 + -1 * P18) === 0) | (!((P17 + -1 * P16) === 0) | (!(P15 === 0) | ((P14 === 0) | (!(P8 === 0) | ((P13 === 0) | ((P12 === 0) | (!(P9 === 0) | ((P11 === 0) | (P10 === 0)))))))))))))))))) | (((P0 === 0) & (!(P2 === 0) & ((P1 === 0) & (!(P3 === 0) & (!(P4 === 0) & (!(P5 === 0) & ((P7 === 0) & (P6 === 0)))))))) & (!((P31 + -1 * P30) === 0) | (!((P29 + -1 * P28) === 0) | (!((P27 + -1 * P26) === 0) | (!((P25 + -1 * P24) === 0) | (!((P23 + -1 * P22) === 0) | (!((P21 + -1 * P20) === 0) | (!((P19 + -1 * P18) === 0) | (!((P17 + -1 * P16) === 0) | (!(P15 === 0) | ((P14 === 0) | (!(P8 === 0) | ((P13 === 0) | ((P12 === 0) | ((!(P11 === 0) | !(P10 === 0)) | (P9 === 0))))))))))))))))) | (((P0 === 0) & (!(P2 === 0) & ((P1 === 0) & (!(P3 === 0) & (!(P4 === 0) & (!(P5 === 0) & ((P7 === 0) & !(P6 === 0)))))))) & (!((P31 + -1 * P30) === 0) | (!((P29 + -1 * P28) === 0) | (!((P27 + -1 * P26) === 0) | (!((P25 + -1 * P24) === 0) | (!((P23 + -1 * P22) === 0) | (!((P21 + -1 * P20) === 0) | (!((P19 + -1 * P18) === 0) | (!((P17 + -1 * P16) === 0) | (!(P15 === 0) | ((P14 === 0) | (!(P8 === 0) | ((P13 === 0) | ((P12 === 0) | ((!(P10 === 0) | (P11 === 0)) | (P9 === 0))))))))))))))))) | (((P0 === 0) & (!(P2 === 0) & (((((!(P7 === 0) & (P6 === 0)) & !(P5 === 0)) & !(P4 === 0)) & !(P3 === 0)) & (P1 === 0)))) & (!((P31 + -1 * P30) === 0) | (!((P29 + -1 * P28) === 0) | (!((P27 + -1 * P26) === 0) | (!((P25 + -1 * P24) === 0) | (!((P23 + -1 * P22) === 0) | (!((P21 + -1 * P20) === 0) | (!((P19 + -1 * P18) === 0) | (!((P17 + -1 * P16) === 0) | (!(P15 === 0) | ((P14 === 0) | (!(P8 === 0) | ((P13 === 0) | ((P12 === 0) | ((!(P11 === 0) | (P10 === 0)) | (P9 === 0)))))))))))))))))
)).toList
)

}} // withProver
