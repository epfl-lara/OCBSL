import scala.collection.mutable
import scala.math.Numeric.IntIsIntegral

/**
 * An EquivalenceChecker is an object that allows to detect equivalence between formulas in the
 * theory of Orthocomplemented Bisemilattices.
 * This allows proof checkers and writers to avoid having to deal with a class of "easy" equivalence.
 * For example, by considering "x ∨ y" as being the same formula as "y ∨ x", we can avoid frustrating errors.
 * This relation is always a subrelation of the usual FOL implication.
 */
object EquivalenceChecker {
    sealed abstract class SimpleFormula {
        val size: Int
        private[EquivalenceChecker] var normalForm: Option[NormalFormula] = None
    }
    case class SConstant(id: String) extends SimpleFormula {
        val size = 1
    }
    case class SNeg(child: SimpleFormula) extends SimpleFormula {
        val size: Int = 1 + child.size
    }
    case class SOr(children: List[SimpleFormula]) extends SimpleFormula {
        val size: Int = (children map (_.size)).foldLeft(1) { case (a, b) => a + b }
    }
    case class SLiteral(b: Boolean) extends SimpleFormula {
        val size = 1
        normalForm = Some(NLiteral(b))
    }
    sealed abstract class NormalFormula {
        val code:Int
    }
    case class NConstant(id: String, code:Int) extends NormalFormula
    case class NNeg(child: NormalFormula, code:Int) extends NormalFormula
    case class NOr(children: List[NormalFormula], code:Int) extends NormalFormula
    case class NLiteral(b: Boolean) extends NormalFormula{
        val code:Int = if (b) 1 else 0
    }

    class LocalEquivalenceChecker {

        private val codesSig: mutable.HashMap[(String, Seq[Int]), Int] = mutable.HashMap()
        codesSig.update(("zero", Nil), 0)
        codesSig.update(("one", Nil), 1)

        def hasNormaleRecComputed(sf:SimpleFormula): Boolean = sf.normalForm.nonEmpty && (sf match {
            case SNeg(child) => hasNormaleRecComputed(child)
            case SOr(children) => children.forall(c => hasNormaleRecComputed(c))
            case _ => true
        })

        def checkForContradiction(children:List[(NormalFormula, Int)]): Boolean = {
            val (negatives_temp, positives) = children.foldLeft[(List[NormalFormula], List[NormalFormula])]((Nil, Nil))(
                (acc, ch) => acc match {
                    case (negatives, positives) => ch._1 match {
                        case NNeg(child, c) =>(child::negatives, positives)
                        case _ => (negatives, ch._1::positives)
                    }
                }
            )
            val negatives = negatives_temp.sortBy(_.code)
            var i, j = 0
            while (i<positives.size && j<negatives.size){ //checks if there is a positive and negative nodes with same code.
                val (c1, c2) = (positives(i).code, negatives(j).code)
                if (c1<c2) i+=1
                else if (c1 == c2) return true
                else j+=1
            }
            val children_codes = children.map(c => c._2).toSet
            var k = 0
            while(k<negatives.size){
                negatives(k) match {
                    case NOr(gdChildren, c) =>
                        if (gdChildren.forall(sf => children_codes.contains(sf.code))) return true
                    case _ => ()
                }
                k+=1
            }
            false
        }

        def updateCodesSig(sig: (String, Seq[Int])): Int = {
            if (!codesSig.contains(sig)) codesSig.update(sig, codesSig.size)
            codesSig(sig)
        }


        def OCBSLCode(phi: SimpleFormula): Int = {
            if (phi.normalForm.nonEmpty) return phi.normalForm.get.code
            val L = pDisj(phi, Nil)
            val L2 = L zip (L map (_.code))
            val L3 = L2.sortBy(_._2).distinctBy(_._2).filterNot(_._2 == 0) //not most efficient on sorted list but no big deal for now
            if (L3.isEmpty) {
                phi.normalForm = Some(NLiteral(false))
            } else if (L3.length == 1) {
                phi.normalForm = Some(L3.head._1)
            } else if (L3.exists(_._2 == 1) || checkForContradiction(L3) ) {
                phi.normalForm = Some(NLiteral(true))
            } else {
                phi.normalForm = Some(NOr(L3.map(_._1), updateCodesSig(("or", L3.map(_._2)))))
            }
            phi.normalForm.get.code
        }

        def pDisj(phi: SimpleFormula, acc: List[NormalFormula]): List[NormalFormula] = {
            if (phi.normalForm.nonEmpty) return pDisjNormal(phi.normalForm.get, acc)
            val r: List[NormalFormula] = phi match {
                case SConstant(id) =>
                    val lab = "pred_" + id
                    phi.normalForm = Some(NConstant(id, updateCodesSig((lab, Nil))))
                    phi.normalForm.get :: acc
                case SNeg(child) => pNeg(child, phi, acc)
                case SOr(children) => children.foldLeft(acc)((p, a) => pDisj(a, p))
                case SLiteral(true) =>
                    phi.normalForm = Some(NLiteral(true))
                    phi.normalForm.get :: acc
                case SLiteral(false) =>
                    phi.normalForm = Some(NLiteral(false))
                    phi.normalForm.get :: acc
            }
            r
        }

        def pNeg(phi: SimpleFormula, parent: SimpleFormula, acc: List[NormalFormula]): List[NormalFormula] = {
            if (phi.normalForm.nonEmpty) return pNegNormal(phi.normalForm.get, parent, acc)
            val r:List[NormalFormula] = phi match {
                case SConstant(id) =>
                    val lab = "pred_" + id
                    phi.normalForm = Some(NConstant(id, updateCodesSig((lab, Nil))))
                    parent.normalForm = Some(NNeg(phi.normalForm.get, updateCodesSig(("neg", List(phi.normalForm.get.code)))))
                    parent.normalForm.get :: acc
                case SNeg(child) => pDisj(child, acc)
                case SLiteral(true) =>
                    parent.normalForm = Some(NLiteral(false))
                    parent.normalForm.get :: acc
                case SLiteral(false) =>
                    parent.normalForm = Some(NLiteral(true))
                    parent.normalForm.get :: acc
                case SOr(children) =>
                    val T = children.sortBy(_.size)
                    val r1 = T.tail.foldLeft(List[NormalFormula]())((p, a) => pDisj(a, p))
                    val r2 = r1 zip (r1 map (_.code))
                    val r3 = r2.sortBy(_._2).distinctBy(_._2).filterNot(_._2 == 0)
                    if (r3.isEmpty) pNeg(T.head, parent, acc)
                    else {
                        val s1 = pDisj(T.head, r1)
                        val s2 = s1 zip (s1 map (_.code))
                        val s3 = s2.sortBy(_._2).distinctBy(_._2).filterNot(_._2 == 0)
                        if (s3.exists(_._2 == 1) || checkForContradiction(s3) ) {
                            phi.normalForm=Some(NLiteral(true))
                            parent.normalForm = Some(NLiteral(false))
                            parent.normalForm.get :: acc
                        } else if (s3.length == 1) {
                            pNegNormal(s3.head._1, parent, acc)
                        } else {
                            phi.normalForm = Some(NOr(s3.map(_._1), updateCodesSig(("or", s3.map(_._2)))))
                            parent.normalForm = Some(NNeg(phi.normalForm.get, updateCodesSig(("neg", List(phi.normalForm.get.code)))))
                            parent.normalForm.get :: acc
                        }
                    }
            }
            r
        }
        def pDisjNormal(f:NormalFormula, acc:List[NormalFormula]):List[NormalFormula] = f match {
            case NOr(children, c) => children ++ acc
            case _ => f :: acc
        }
        def pNegNormal(f:NormalFormula, parent: SimpleFormula, acc:List[NormalFormula]): List[NormalFormula] = f match {
            case NNeg(child, c) =>
                pDisjNormal(child, acc)
            case _ =>
                parent.normalForm = Some(NNeg(f, updateCodesSig(("neg", List(f.code)))))
                parent.normalForm.get :: acc
        }

        def checkEquivalence(formula1: SimpleFormula, formula2: SimpleFormula): Boolean = {
            getCode(formula1) == getCode(formula2)
        }
        def getCode(formula:SimpleFormula): Int = OCBSLCode(formula)

    }


    def isSame(formula1: SimpleFormula, formula2: SimpleFormula): Boolean = (new LocalEquivalenceChecker).checkEquivalence(formula1, formula2)
}
