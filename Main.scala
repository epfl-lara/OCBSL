import EquivalenceChecker._
object Main {

    def main(args: Array[String]):Unit = {

        val positiveTestCases: List[(SimpleFormula, SimpleFormula)] = List(
            and(a, b) -> and(b, a),
            or(a, b) -> or(b, a),
            iff(a, b) -> iff(b, a),
            and(and(a, b), c) -> and(a, and(b, c)),
            or(or(a, b), c) -> or(a, or(b, c)),
            neg(a) -> neg(neg(neg(a))),
            a -> neg(neg(neg(neg(a)))),
            and(a, b) -> neg(or(neg(a), neg(b))),
            or(a, b) -> neg(and(neg(a), neg(b))),
            or(a, neg(a)) -> or(neg(a), neg(neg(a))),
            and(a, neg(a)) -> and(neg(a), neg(neg(a))),
            and(a, a) -> a,
            or(a, a) -> a
        )

        val negativeTestCases: List[(SimpleFormula, SimpleFormula)] = List(
            a -> implies(a, x),
            a -> iff(a, x),
            and(a, or(x, y)) -> or(and(a, x), and(a, y)),
            or(a, and(x, y)) -> and(or(a, x), or(a, y)),
        )
        println("Positive Test Cases")
        positiveTestCases.foreach{ case (f,g) => println(isSame(f,g))}
        println("Negative Test Cases")
        negativeTestCases.foreach{ case (f,g) => println(isSame(f,g))}

    }

    val a = SConstant("a")
    val b = SConstant("b")
    val c = SConstant("c")
    val x = SConstant("x")
    val y = SConstant("y")
    def neg(f:SimpleFormula):SimpleFormula = SNeg(f)
    def and(args:List[SimpleFormula]): SimpleFormula = SNeg(SOr(args.map(c => SNeg(c))))
    def and(f:SimpleFormula, g:SimpleFormula): SimpleFormula = and(List(f,g))
    def or(args:List[SimpleFormula]): SimpleFormula = SOr(args)
    def or(f:SimpleFormula, g:SimpleFormula): SimpleFormula = or(List(f,g))
    def iff(f:SimpleFormula, g:SimpleFormula): SimpleFormula = and(implies(f,g), implies(g,f))
    def implies(f:SimpleFormula, g:SimpleFormula): SimpleFormula = SNeg(or(SNeg(f),g))
}
