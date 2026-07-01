package synth262.interpreter

import synth262.ir.Global
import synth262.util.BaseUtils.*
import scala.math.{BigInt => SBigInt}

/** extensions for Double */
extension (l: Double) {
  def %%(r: Double): Double =
    val m = l % r
    if (m * r < 0.0) m + r else m
}

/** extensions for scala.math.BigInt */
extension (l: SBigInt) {
  def %%(r: SBigInt): SBigInt =
    val m = l % r
    if (m * r < 0) m + r else m
}

/** extensions for BigDecimal */
extension (l: BigDecimal) {
  def %%(r: BigDecimal): BigDecimal =
    val m = l % r
    if (m * r < 0) m + r else m
}
