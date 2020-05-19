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

  def toListWithFoldRight: List[A] =
    foldRight(List.empty)(_ :: _)

  def take(n: Int): Stream[A] =
    if (n <= 0) empty[A]
    else
      this match {
        case Empty      => empty[A]
        case Cons(h, t) => cons(h(), t().take(n - 1))
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
    case Cons(h, t) if p(h()) => cons(h(), t().takeWhile(p))
    case Cons(_, t)           => t().takeWhile(p)
  }

  def forAll(p: A => Boolean): Boolean =
    foldRight(true)((a, b) => p(a) && b)

  def takeWhileWithFoldRight(p: A => Boolean): Stream[A] =
    foldRight(Stream.empty[A])((item, acc) => if (p(item)) cons(item, acc) else acc)

  def headOption: Option[A] =
    foldRight(None: Option[A])((h, _) => Some(h))

  // 5.7 map, filter, append, flatmap using foldRight. Part of the exercise is
  // writing your own function signatures.

  def map[B](f: A => B): Stream[B] =
    foldRight(empty[B])((h, t) => cons(f(h), t))

  def filter(f: A => Boolean): Stream[A] =
    foldRight(empty[A])((h, t) => if (f(h)) cons(h, t) else t)

  def append[B>:A](other: Stream[B]): Stream[B] =
    foldRight(other)((h, t) => cons(h, t))

  def flatMap[B](f: A => Stream[B]): Stream[B] =
    foldRight(empty[B])((h, t) => f(h).append(t))

  def startsWith[B](s: Stream[B]): Boolean = ???
}
case object Empty extends Stream[Nothing]
case class Cons[+A](h: () => A, t: () => Stream[A]) extends Stream[A]

object Stream {
  def cons[A](hd: => A, tl: => Stream[A]): Stream[A] = {
    lazy val head = hd
    lazy val tail = tl
    Cons(() => head, () => tail)
  }

  def empty[A]: Stream[A] = Empty

  def apply[A](as: A*): Stream[A] =
    if (as.isEmpty) empty
    else cons(as.head, apply(as.tail: _*))

  val ones: Stream[Int] = Stream.cons(1, ones)
  def from(n: Int): Stream[Int] = ???

  def unfold[A, S](z: S)(f: S => Option[(A, S)]): Stream[A] = ???
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
