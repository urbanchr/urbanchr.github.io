// CW 1



abstract class Rexp
case object ZERO extends Rexp
case object ONE extends Rexp
case class CHAR(c: Char) extends Rexp
case class ALT(r1: Rexp, r2: Rexp) extends Rexp 
case class SEQ(r1: Rexp, r2: Rexp) extends Rexp 
case class STAR(r: Rexp) extends Rexp 
 
case class RANGE(cs: Set[Char]) extends Rexp             // set of characters
case class PLUS(r: Rexp) extends Rexp                    // plus
case class OPTIONAL(r: Rexp) extends Rexp                // optional
case class INTER(r1: Rexp, r2: Rexp) extends Rexp        // intersection
case class NTIMES(r: Rexp, n: Int) extends Rexp          // n-times
case class UPTO(r: Rexp, n: Int) extends Rexp            // up n-times
case class FROM(r: Rexp, n: Int) extends Rexp            // from n-times
case class BETWEEN(r: Rexp, n: Int, m: Int) extends Rexp // between nm-times
case class NOT(r: Rexp) extends Rexp                     // not
case class CFUN(f: Char => Boolean) extends Rexp         // subsuming CHAR and RANGE

def FCHAR(c: Char) = CFUN(c == _)
val FALL = CFUN(_ => true)
def FRANGE(cs: Set[Char]) = CFUN(cs.contains(_))

// the nullable function: tests whether the regular 
// expression can recognise the empty string
def nullable (r: Rexp) : Boolean = r match {
  case ZERO => false
  case ONE => true
  case CHAR(_) => false
  case ALT(r1, r2) => nullable(r1) || nullable(r2)
  case SEQ(r1, r2) => nullable(r1) && nullable(r2)
  case STAR(_) => true
  case RANGE(_) => false
  case PLUS(r) => nullable(r)
  case OPTIONAL(_) => true
  case INTER(r1, r2) => nullable(r1) && nullable(r2)
  case NTIMES(r, n) => if (n == 0) true else nullable(r)
  case UPTO(_, _) => true
  case FROM(r, n) => if (n == 0) true else nullable(r)
  case BETWEEN(r, n, m) => if (n == 0) true else nullable(r)
  case NOT(r) => !nullable(r)
  case CFUN(_) => false
}

// the derivative of a regular expression w.r.t. a character
def der(c: Char, r: Rexp) : Rexp = r match {
  case ZERO => ZERO
  case ONE => ZERO
  case CHAR(d) => if (c == d) ONE else ZERO
  case ALT(r1, r2) => ALT(der(c, r1), der(c, r2))
  case SEQ(r1, r2) => 
    if (nullable(r1)) ALT(SEQ(der(c, r1), r2), der(c, r2))
    else SEQ(der(c, r1), r2)
  case STAR(r1) => SEQ(der(c, r1), STAR(r1))
  case RANGE(cs) => if (cs contains c) ONE else ZERO
  case PLUS(r) => SEQ(der(c, r), STAR(r))
  case OPTIONAL(r) => der(c, r)
  case INTER(r1, r2) => INTER(der(c, r1), der(c, r2))
  case NTIMES(r, n) => 
    if (n == 0) ZERO else SEQ(der(c, r), NTIMES(r, n - 1))
  case UPTO(r, n) =>
    if (n == 0) ZERO else SEQ(der(c, r), UPTO(r, n - 1))
  case FROM(r, n) =>
    if (n == 0) SEQ(der(c, r), FROM(r, 0)) else SEQ(der(c, r), FROM(r, n - 1))
  case BETWEEN(r, n, m) =>
    if (m == 0) ZERO else 
    if (n == 0) SEQ(der(c, r), UPTO(r, m - 1)) 
    else SEQ(der(c, r), BETWEEN(r, n - 1, m - 1)) 
  case NOT(r) => NOT(der (c, r))
  case CFUN(f) => if (f(c)) ONE else ZERO
}

// simplification
def simp(r: Rexp) : Rexp = r match {
  case ALT(r1, r2) => (simp(r1), simp(r2)) match {
    case (ZERO, r2s) => r2s
    case (r1s, ZERO) => r1s
    case (r1s, r2s) => if (r1s == r2s) r1s else ALT (r1s, r2s)
  }
  case SEQ(r1, r2) =>  (simp(r1), simp(r2)) match {
    case (ZERO, _) => ZERO
    case (_, ZERO) => ZERO
    case (ONE, r2s) => r2s
    case (r1s, ONE) => r1s
    case (r1s, r2s) => SEQ(r1s, r2s)
  }
  case r => r
}

// the derivative w.r.t. a string (iterates der)
def ders(s: List[Char], r: Rexp) : Rexp = s match {
  case Nil => r
  case c::s => ders(s, simp(der(c, r)))
}

// the main matcher function
def matcher(r: Rexp, s: String) : Boolean = 
  nullable(ders(s.toList, r))


// Test Cases
//============

// some syntactic convenience

def charlist2rexp(s: List[Char]) : Rexp = s match {
  case Nil => ONE
  case c::Nil => CHAR(c)
  case c::s => SEQ(CHAR(c), charlist2rexp(s))
}
implicit def string2rexp(s: String) : Rexp = charlist2rexp(s.toList)

extension (r: Rexp) {
  def | (s: Rexp) = ALT(r, s)
  def ~ (s: Rexp) = SEQ(r, s)
  def % = STAR(r)
}


println("EMAIL:")
val LOWERCASE = ('a' to 'z').toSet
val DIGITS = ('0' to '9').toSet
val SYMBOLS1 = ("_.-").toSet
val SYMBOLS2 = (".-").toSet
val EMAIL = { PLUS(CFUN(LOWERCASE | DIGITS | SYMBOLS1)) ~ "@" ~ 
              PLUS(CFUN(LOWERCASE | DIGITS | SYMBOLS2)) ~ "." ~
              BETWEEN(CFUN(LOWERCASE | Set('.')), 2, 6) }

val my_email = "christian.urban@kcl.ac.uk"

println(EMAIL);
println(matcher(EMAIL, my_email))
println(ders(my_email.toList,EMAIL))

val ALL = CFUN((c:Char) => true)
val COMMENT = "/*" ~ (NOT(ALL.% ~ "*/" ~ ALL.%)) ~ " * /"

println(matcher(COMMENT, "/**/"))
println(matcher(COMMENT, "/*foobar*/"))
println(matcher(COMMENT, "/*test*/test*/"))
println(matcher(COMMENT, "/*test/*test*/"))

