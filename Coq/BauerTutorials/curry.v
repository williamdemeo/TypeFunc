(** Currying and uncurrying.  Based on Andrej Bauer's tutorial at:
    http://www.youtube.com/watch?v=i2Q5GJhgsjA&list=PLDD40A96C2ED54E99&feature=share&index=6
*)

Parameters A B C : Set.   (* Assume we have 3 sets, A, B, and C. *)

(* A function f : A x B -> C is equivalent to a function of type A -> (B -> C) *)
Definition curry(f : A * B -> C) := fun a => fun b => f(a, b).
Definition uncurry(g : A -> B -> C) := fun p => g (fst p) (snd p).

Theorem uncurry_curry_is_id : forall f a b, uncurry (curry f) (a, b) = f (a, b).
Proof.
  intros.
  unfold curry, uncurry.
  simpl.
  reflexivity.
Qed.

Theorem curry_uncurry_is_id : forall f a b, curry (uncurry f) a b = f a b.
Proof.
  intros.
  unfold curry, uncurry.
  simpl.
  reflexivity.
Qed.

(* left off at 2'30" *)