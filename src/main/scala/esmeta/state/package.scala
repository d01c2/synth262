package esmeta.state

import esmeta.state.util.*
import esmeta.util.BaseUtils.*
import esmeta.ir.Global
import esmeta.parser.ESParser
import java.math.MathContext.{UNLIMITED, DECIMAL128}

/** IR state elements */
trait StateElem {
  override def toString: String = toString(true, false)

  /** stringify with options */
  def toString(detail: Boolean = true, location: Boolean = false): String =
    val stringifier = StateElem.getStringifier(detail, location)
    import stringifier.elemRule
    stringify(this)
}
object StateElem {
  val getStringifier =
    cached[(Boolean, Boolean), Stringifier] { Stringifier(_, _) }
}

/** predefined enums */
val ENUM_EMPTY = Enum("empty")
val ENUM_UNRESOLVABLE = Enum("unresolvable")
val ENUM_LEXICAL = Enum("lexical")
val ENUM_INITIALIZED = Enum("initialized")
val ENUM_UNINITIALIZED = Enum("uninitialized")
val ENUM_BASE = Enum("base")
val ENUM_DERIVED = Enum("derived")
val ENUM_STRICT = Enum("strict")
val ENUM_GLOBAL = Enum("global")
val ENUM_UNLINKED = Enum("unlinked")
val ENUM_LINKING = Enum("linking")
val ENUM_LINKED = Enum("linked")
val ENUM_EVALUATING = Enum("evaluating")
val ENUM_EVALUATED = Enum("evaluated")
val ENUM_NUMBER = Enum("Number")
val ENUM_BIGINT = Enum("BigInt")
val ENUM_NORMAL = Enum("normal")
val ENUM_BREAK = Enum("break")
val ENUM_CONTINUE = Enum("continue")
val ENUM_RETURN = Enum("return")
val ENUM_THROW = Enum("throw")
val ENUM_SUSPENDED_START = Enum("suspendedStart")
val ENUM_SUSPENDED_YIELD = Enum("suspendedYield")
val ENUM_EXECUTING = Enum("executing")
val ENUM_AWAITING_RETURN = Enum("awaitingDASHreturn")
val ENUM_COMPLETED = Enum("completed")
val ENUM_PENDING = Enum("pending")
val ENUM_FULFILLED = Enum("fulfilled")
val ENUM_REJECTED = Enum("rejected")
val ENUM_FULFILL = Enum("Fulfill")
val ENUM_REJECT = Enum("Reject")

/** predefined identifiers */
val GLOBAL_RESULT = Global("RESULT")

/** predefined string */
val STR_TOP_LEVEL = "TOP_LEVEL"

/** predefined values */
val POS_INF = Infinity(pos = true)
val NEG_INF = Infinity(pos = false)
val NUMBER_POS_INF = Number(Double.PositiveInfinity)
val NUMBER_NEG_INF = Number(Double.NegativeInfinity)

def trimString(x: String, isStarting: Boolean, esParser: ESParser): String =
  val sb = new java.lang.StringBuilder
  val arr = {
    // NOTE x.codePoints is not compatible with Scala.js, Using a cross-platform alternative.
    val len = x.codePointCount(0, x.length)
    val arr = Array.ofDim[Int](len)
    var charIndex = 0
    var cpIndex = 0
    while (charIndex < x.length) {
      val cp = x.codePointAt(charIndex)
      arr(cpIndex) = cp
      charIndex += Character.charCount(cp)
      cpIndex += 1
    }
    arr
  }
  val cps = esParser.WhiteSpaceCPs ++ esParser.LineTerminatorCPs
  def find(i: Int, next: Int => Int): Int =
    if (i < 0 || i >= arr.length) i
    else if (cps contains arr(i)) find(next(i), next)
    else i
  val start = if (isStarting) find(0, _ + 1) else 0
  val end = if (isStarting) arr.length else find(arr.length - 1, _ - 1)
  arr.slice(start, end + 1).foreach(sb.appendCodePoint)
  sb.toString

/** conversion number to string */
// NOTE: Number::toString ( x, radix )
def toStringHelper(x: Double, radix: Int = 10): String = {
  // get sign
  def getSign(n: Int): Char = if (n - 1 > 0) '+' else '-'

  // get string of number
  def getStr(number: scala.math.BigInt, radix: Int): String =
    var str = ""
    var s = number
    while (s > 0) { str += getRadixString(s % radix); s /= radix }
    str.reverse

  // get radix string of number
  def getRadixString(d: scala.math.BigInt): String =
    if (d < 10) d.toString else ('a' + (d - 10)).toChar.toString

  // 1. If _x_ is *NaN*, return *"NaN"*.
  if (x.isNaN) "NaN"
  // 2. If _x_ is either *+0*<sub>𝔽</sub> or *-0*<sub>𝔽</sub>, return *"0"*.
  else if (x == 0) "0"
  // 3. If _x_ < *-0*<sub>𝔽</sub>, return the string-concatenation of *"-"*
  //    and toStringHelper(-_x_, _radix_).
  else if (x < 0) "-" + toStringHelper(-x, radix)
  // 4. If _x_ is *+∞*<sub>𝔽</sub>, return *"Infinity"*.
  else if (x.isPosInfinity) "Infinity"
  else {
    // 5. Let _n_, _k_, and _s_ be integers such that _k_ ≥ 1,
    //    _radix_^(_k_ - 1) ≤ _s_ < _radix_^_k_, 𝔽(_s_ × _radix_^(_n_ - _k_))
    //    is _x_, and _k_ is as small as possible. Note that _k_ is the
    //    number of digits in the representation of _s_ using radix _radix_,
    //    that _s_ is not divisible by _radix_, and that the least significant
    //    digit of _s_ is not necessarily uniquely determined by these criteria.
    val (n: Int, k: Int, s: scala.math.BigInt) =
      if (radix == 10)
        // For radix 10, the exact decimal representation of an IEEE 754
        // double is always a finite decimal, so the BigDecimal algorithm
        // terminates and finds the exact (n, k, s).
        var S = BigDecimal(x, UNLIMITED)
        var N = 0
        while (S % radix == 0) { S /= radix; N += 1 }
        while (S % 1 != 0) { S *= radix; N -= 1 }
        var RK = BigDecimal(radix, UNLIMITED)
        var K = 1
        while (S >= RK) { RK *= radix; K += 1 }
        (N + K, K, S.toBigInt)
      else
        // For non-10 radixes, the BigDecimal approach can loop forever
        // because the exact decimal of a double (m × 2^e) may not be a
        // finite base-R fraction when R has prime factors other than
        // 2 and 5 (e.g., radix=3, x=0.1). Instead, directly search for
        // the minimal k where 𝔽(s × radix^(n-k)) = x, using exact
        // binary arithmetic.
        import scala.math.{BigInt => SBigInt, BigDecimal => SBigDec}

        // extract exact IEEE 754 binary representation: x = mant × 2^bExp
        val bits = java.lang.Double.doubleToLongBits(x)
        val rawExp = ((bits >>> 52) & 0x7ff).toInt
        val mant = SBigInt(
          if (rawExp == 0) bits & 0xfffffffffffffL
          else (bits & 0xfffffffffffffL) | 0x10000000000000L,
        )
        val bExp = if (rawExp == 0) 1 - 1023 - 52 else rawExp - 1023 - 52

        val bigR = SBigInt(radix)
        val mc = new java.math.MathContext(200)

        // round-to-nearest integer division for positive BigInts
        def divRound(num: SBigInt, den: SBigInt): SBigInt =
          (num * 2 + den) / (den * 2)

        // compute s = round(x / radix^p) = round(mant × 2^bExp / radix^p)
        def computeS(p: Int): SBigInt =
          val rp = bigR.pow(scala.math.abs(p))
          if (p >= 0 && bExp >= 0) divRound(mant << bExp, rp)
          else if (p >= 0) divRound(mant, SBigInt(2).pow(-bExp) * rp)
          else if (bExp >= 0) (mant << bExp) * rp
          else divRound(mant * rp, SBigInt(2).pow(-bExp))

        // check 𝔽(s × radix^p) == x
        def checkTrip(s: SBigInt, p: Int): Boolean =
          if (p >= 0) SBigDec(s * bigR.pow(p)).doubleValue == x
          else (SBigDec(s, mc) / SBigDec(bigR.pow(-p), mc)).doubleValue == x

        // exact comparison: x ≥ radix^e, using BigInteger arithmetic
        // to avoid floating-point imprecision in log-based estimates
        def xGeRadixPow(e: Int): Boolean =
          if (e >= 0 && bExp >= 0)
            (mant << bExp) >= bigR.pow(e)
          else if (e >= 0) // bExp < 0
            mant >= bigR.pow(e) * SBigInt(2).pow(-bExp)
          else if (bExp >= 0) // e < 0
            (mant << bExp) * bigR.pow(-e) >= 1
          else // e < 0, bExp < 0
            mant * bigR.pow(-e) >= SBigInt(2).pow(-bExp)

        // determine n such that radix^(n-1) ≤ x < radix^n
        var N = scala.math
          .floor(java.lang.Math.log(x) / java.lang.Math.log(radix.toDouble))
          .toInt + 1
        while (!xGeRadixPow(N - 1)) N -= 1
        while (xGeRadixPow(N)) N += 1

        // search for minimal k (bounded by 54 for 53-bit mantissa)
        var K = 1
        var S: SBigInt = SBigInt(0)
        var found = false
        while (!found && K <= 54)
          val p = N - K
          S = computeS(p)
          val lo = bigR.pow(K - 1)
          val hi = lo * radix
          if (S < lo || S >= hi) K += 1
          else if (checkTrip(S, p)) found = true
          else if (S + 1 < hi && checkTrip(S + 1, p))
            S += 1; found = true
          else if (S - 1 >= lo && checkTrip(S - 1, p))
            S -= 1; found = true
          else K += 1
        // ensure _s_ is not divisible by _radix_
        while (S % radix == 0 && K > 1) { S /= radix; K -= 1 }
        (N, K, S)

    // 6. If _radix_ ≠ 10 or _n_ is in the inclusive interval from -5 to 21,
    //    then
    if (radix != 10 || (-6 < n && n <= 21)) {
      // 6.a. If _n_ ≥ _k_, then
      if (k <= n) {
        getStr(s, radix) +
        "0" * (n - k)
        // 6.b. Else if _n_ > 0, then
      } else if (n > 0) {
        val str = getStr(s, radix)
        str.substring(0, n) +
        '.' +
        str.substring(n)
        // 6.c. Else,
      } else {
        "0" +
        "." +
        "0" * -n +
        getStr(s, radix)
      }
    } else {
      // 7. NOTE: In this case, the input will be represented using scientific
      //    E notation, such as 1.2e+3.
      // 8. Assert: _radix_ is 10.
      // 9. If _n_ < 0, then let _exponentSign_ be 0x002D (HYPHEN-MINUS).
      // 10. Else, let _exponentSign_ be 0x002B (PLUS SIGN).
      val exponentSign = getSign(n)
      // 11. If _k_ = 1, then return the string-concatenation of:
      if (k == 1) {
        // * the code unit of the single digit of _s_
        getStr(s, radix) +
        // * the code unit 0x0065 (LATIN SMALL LETTER E)
        "e" +
        // * _exponentSign_
        exponentSign +
        // * the code units of the decimal representation of abs(_n_ - 1)
        math.abs(n - 1)
        // 12. Return the string-concatenation of:
      } else {
        val str = getStr(s, radix)
        // * the code unit of the most significant digit of the decimal
        //   representation of _s_
        str.substring(0, 1) +
        // * the code unit 0x002E (FULL STOP)
        '.' +
        // * the code units of the remaining _k_ - 1 digits of the decimal
        //   representation of _s_
        str.substring(1) +
        // * the code unit 0x0065 (LATIN SMALL LETTER E)
        'e' +
        // * _exponentSign_
        exponentSign +
        // * the code units of the decimal representation of abs(_n_ - 1)
        math.abs(n - 1)
      }
    }
  }
}

// -----------------------------------------------------------------------------
// types
// -----------------------------------------------------------------------------
type Undef = Undef.type
type Null = Null.type
