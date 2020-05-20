package fpinscala.laziness

import Stream._
trait Stream[+A] {

  def foldRight[B](z: => B)(f: (A, => B) => B): B = // The arrow `=>` in front of the argument type `B` means that the function `f` takes its second argument by name and may choose not to evaluate it.
    this match {
      case Cons(h, t) =>
        f(h(), t().foldRight(z)(f)) // If `f` doesn't evaluate its second argument, the recursion never occurs.
      case _ => z
    }

  def exists(p: A => Boolean): Boolean =
    foldRight(false)((a, b) => p(a) || b) // Here `b` is the unevaluated recursive step that folds the tail of the stream. If `p(a)` returns `true`, `b` will never be evaluated and the computation terminates early.

  @annotation.tailrec
  final def find(f: A => Boolean): Option[A] = this match {
    case Empty      => None
    case Cons(h, t) => if (f(h())) Some(h()) else t().find(f)
  }

  def toList: List[A] = this match {
    case Empty      => List.empty
    case Cons(h, t) => h() :: t().toList
  }

  def take(n: Int): Stream[A] =
    if (n <= 0) empty[A]
    else
      this match {
        case Empty      => empty[A]
        case Cons(h, t) => cons(() => h(), () => t().take(n - 1))
      }

  def takeUnfold(n: Int): Stream[A] =
    unfold((this, n)) {
      case (_, i) if i <= 0 => None
      case (Cons(h, _), 1) => Some( (h(), (empty, 0)) )
      case (Cons(h, t), i) => Some( (h(), (t(), i-1)) )
    }

  def drop(n: Int): Stream[A] =
    if (n <= 0) this
    else
      this match {
        case Empty      => empty[A]
        case Cons(_, t) => t().drop(n - 1)
      }

  def takeWhile(p: A => Boolean): Stream[A] = this match {
    case Empty                => Stream.empty
    case Cons(h, t) if p(h()) => cons(() => h(), () => t().takeWhile(p))
    case Cons(_, t)           => t().takeWhile(p)
  }

  def takeWhileUnfold(p: A => Boolean): Stream[A] =
    unfold(this) {
      case Cons(h, t) if p(h()) => Some( (h(), t()) )
      case _ => None
    }

  def forAll(p: A => Boolean): Boolean =
    foldRight(true)((a, b) => p(a) && b)

  def takeWhileWithFoldRight(p: A => Boolean): Stream[A] =
    foldRight(Stream.empty[A])((item, acc) => if (p(item)) cons(() => item, () => acc) else acc)

  def headOption: Option[A] =
    foldRight(None: Option[A])((h, _) => Some(h))

  // 5.7 map, filter, append, flatmap using foldRight. Part of the exercise is
  // writing your own function signatures.

  def map[B](f: A => B): Stream[B] =
    foldRight(empty[B])((h, t) => cons(() => f(h), () => t))

  def map2[B](f: A => B): Stream[B] = this match {
    case Empty => empty[B]
    case Cons(h, t) => cons(() => f(h()), () => t().map2(f))
  }

  def mapUnfold[B](f: A => B): Stream[B] =
    unfold(this) {
      case Cons(h, t) => Some((f(h()), t()))
      case _ => None
    }

  def filter(f: A => Boolean): Stream[A] =
    foldRight(empty[A])((h, t) => if (f(h)) cons(() => h, () => t) else t)

  def filter2(f: A => Boolean): Stream[A] = this match {
    case Empty => empty[A]
    case Cons(h, t) => if (f(h())) cons(() => h(), () => t()) else t()
  }

  def find2(p: A => Boolean): Option[A] =
    filter(p).headOption

  def append[B>:A](other: Stream[B]): Stream[B] =
    foldRight(other)((h, t) => cons(() => h, () => t))

  def flatMap[B](f: A => Stream[B]): Stream[B] =
    foldRight(empty[B])((h, t) => f(h).append(t))

  def startsWith[B](s: Stream[B]): Boolean =
    zipAll(s).takeWhile(_._2.isDefined) forAll {
      case (h, h2) => h == h2
    }

  def zipWith[B, C](other: Stream[B])(f: (A, B) => C): Stream[C] =
    unfold((this, other)) {
      case (Cons(h1, t1), Cons(h2, t2)) => Some( (f(h1(), h2()), (t1(), t2())) )
      case _ => None
    }

  def zipAll[B](other: Stream[B]): Stream[(Option[A], Option[B])] =
    unfold((this, other)) {
      case (Empty, Empty) => None
      case (Cons(h1, t1), Empty) => Some( (Some(h1()), Option.empty[B]) -> (t1(), empty[B]) )
      case (Empty, Cons(h2, t2)) => Some( (Option.empty[A], Some(h2())) -> (empty[A], t2()) )
      case (Cons(h1, t1), Cons(h2, t2)) => Some( (Some(h1()), Some(h2())) -> (t1(), t2()) )
    }

  def tails: Stream[Stream[A]] =
    unfold(this) {
      case Empty => None
      case s => Some( s -> s.drop(1) )
    } append Stream(empty)

  def hasSubsequence[A](s: Stream[A]): Boolean =
    tails exists (_ startsWith s)

}
case object Empty extends Stream[Nothing]
case class Cons[+A](h: () => A, t: () => Stream[A]) extends Stream[A]

object Stream {
  def cons[A](hd: () => A, tl: () => Stream[A]): Stream[A] = {
    lazy val head = hd()
    lazy val tail = tl()
    Cons(() => head, () => tail)
  }

  def empty[A]: Stream[A] = Empty

  def apply[A](as: A*): Stream[A] =
    if (as.isEmpty) empty
    else cons(() => as.head, () => apply(as.tail: _*))

  val ones: Stream[Int] =
    Stream.cons(() => 1, () => ones)

  def constant[A](a: A): Stream[A] =
    Stream.cons(() => a, () => constant(a))

  def from(n: Int): Stream[Int] =
    Stream.cons(() => n, () => from(n + 1))

  def fibs(a: Int = 0, b: Int = 1): Stream[Int] =
    Stream.cons(() => a, () => fibs(b, a + b))

  def unfold[A, S](z: S)(f: S => Option[(A, S)]): Stream[A] = f(z) match {
    case None => Stream.empty
    case Some((a, s)) => Stream.cons(() => a, () => unfold(s)(f))
  }

  def onesUnfold: Stream[Int] =
    unfold(1)(one => Some((one, one)))

  def from(n: Int): Stream[Int] =
    unfold(n)(i => Some((i, i + 1)))

  def fromUnfold(n: Int): Stream[Int] =
    unfold(n)(i => Some((i, i + 1)))

  def fibsUnfold: Stream[Int] =
    unfold((0, 1)) { case (a, b) => Some((a, (b, a + b)))
}

object Test extends App {
  val st: Stream[Int] = Stream(1, 2, 3, 4)
  val ls: List[Int] = st.toList
  println(ls)
  println(st.take(2).toList)
  println(st.drop(2).toList)
  println(st.takeWhile(_ % 2 == 0).toList)
  println(st.takeWhileWithFoldRight(_ % 2 == 0).toList)
  println(st.map(_ + 10).toList)
  println(st.append(Stream(5,6,7,8)).toList)
}
